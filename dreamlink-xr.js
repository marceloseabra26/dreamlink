/*
 * DreamLink XR — controle Google Daydream como controle VR nativo no WebXR.
 *
 * Conecta no controle por Web Bluetooth e o apresenta à página como um controle rastreado
 * ("tracked-pointer"), igual a um controle de Quest. Funciona em páginas WebXR comuns
 * (PlayCanvas/SuperSplat, three.js, A-Frame, Babylon), inclusive quando o visualizador roda
 * num quadro (iframe) do mesmo domínio.
 *
 * Mapeamento no SuperSplat:
 *   apontar o controle ........ mira do teleporte
 *   clique no touchpad ........ segurar = mostra o arco · soltar = teleporta
 *   deslizar ↑ / ↓ no touch ... andar para frente / para trás
 *   deslizar ← / → no touch ... girar 45°
 *   Home ...................... recentralizar (aponte para frente e aperte)
 *
 * Uso: como <script> no <head> antes do viewer, ou como favorito (bookmarklet) rodado
 * na página aberta ANTES de entrar no VR.
 */
(function (root) {
    'use strict';
    if (root.dreamlinkXR) {
        root.dreamlinkXR.showUi();
        return;
    }

    // ---------------------------------------------------------------- protocolo
    const SERVICE = 0xfe55;
    const DATA_CHAR = '00000001-1000-1000-8000-00805f9b34fb';

    const ORI = (2 * Math.PI) / 4095;
    const ACC = (8 * 9.8) / 4095;
    const GYR = ((2048 / 180) * Math.PI) / 4095;
    const s13 = (v) => (v << 19) >> 19;

    // mesmo mapa de bits validado no app Android
    function parse(dv) {
        if (dv.byteLength < 20) return null;
        const b = (i) => dv.getUint8(i);
        const ox = s13(((b(1) & 0x03) << 11) | (b(2) << 3) | ((b(3) & 0xe0) >> 5));
        const oy = s13(((b(3) & 0x1f) << 8) | b(4));
        const oz = s13((b(5) << 5) | ((b(6) & 0xf8) >> 3));
        const ax = s13(((b(6) & 0x07) << 10) | (b(7) << 2) | ((b(8) & 0xc0) >> 6));
        const ay = s13(((b(8) & 0x3f) << 7) | ((b(9) & 0xfe) >> 1));
        const az = s13(((b(9) & 0x01) << 12) | (b(10) << 4) | ((b(11) & 0xf0) >> 4));
        const gx = s13(((b(11) & 0x0f) << 9) | (b(12) << 1) | ((b(13) & 0x80) >> 7));
        const gy = s13(((b(13) & 0x7f) << 6) | ((b(14) & 0xfc) >> 2));
        const gz = s13(((b(14) & 0x03) << 11) | (b(15) << 3) | ((b(16) & 0xe0) >> 5));
        const tx = ((b(16) & 0x1f) << 3) | ((b(17) & 0xe0) >> 5);
        const ty = ((b(17) & 0x1f) << 3) | ((b(18) & 0xe0) >> 5);
        const btn = b(18);
        return {
            ori: [ox * ORI, oy * ORI, oz * ORI],
            acc: [ax * ACC, ay * ACC, az * ACC],
            gyro: [gx * GYR, gy * GYR, gz * GYR],
            tx: tx / 255,
            ty: ty / 255,
            touching: tx !== 0 || ty !== 0,
            click: (btn & 0x01) !== 0,
            home: (btn & 0x02) !== 0,
            app: (btn & 0x04) !== 0,
            volDown: (btn & 0x08) !== 0,
            volUp: (btn & 0x10) !== 0
        };
    }

    // ---------------------------------------------------------------- quatérnios [x,y,z,w]
    const qMul = (a, b) => [
        a[3] * b[0] + a[0] * b[3] + a[1] * b[2] - a[2] * b[1],
        a[3] * b[1] - a[0] * b[2] + a[1] * b[3] + a[2] * b[0],
        a[3] * b[2] + a[0] * b[1] - a[1] * b[0] + a[2] * b[3],
        a[3] * b[3] - a[0] * b[0] - a[1] * b[1] - a[2] * b[2]
    ];
    const qConj = (q) => [-q[0], -q[1], -q[2], q[3]];
    const qNorm = (q) => {
        const l = Math.hypot(q[0], q[1], q[2], q[3]) || 1;
        return [q[0] / l, q[1] / l, q[2] / l, q[3] / l];
    };
    const qRot = (q, v) => {
        const r = qMul(qMul(q, [v[0], v[1], v[2], 0]), qConj(q));
        return [r[0], r[1], r[2]];
    };
    const qFromAxisAngle = (v) => {
        const a = Math.hypot(v[0], v[1], v[2]);
        if (a < 1e-6) return [0, 0, 0, 1];
        const s = Math.sin(a / 2) / a;
        return [v[0] * s, v[1] * s, v[2] * s, Math.cos(a / 2)];
    };
    // só a rotação em torno do eixo vertical (para onde se olha no plano do chão)
    const qYaw = (q) => {
        const f = qRot(q, [0, 0, -1]);
        const yaw = Math.atan2(-f[0], -f[2]);
        return [0, Math.sin(yaw / 2), 0, Math.cos(yaw / 2)];
    };
    // A ponta do controle já é o -Z, igual ao WebXR (confirmado no teste real no SuperSplat).
    const controllerQuat = (ori) => qNorm(qFromAxisAngle(ori));

    // ---------------------------------------------------------------- estado
    const ctl = { device: null, connected: false, state: null, battery: null, packets: 0, pps: 0 };
    let session = null; // sessão VR ativa
    let sessionWin = null; // janela (página ou quadro) dona da sessão
    let injected = false;
    let recenterPending = true;
    let R = [0, 0, 0, 1]; // alinhamento horizontal controle → mundo, definido no recentro
    const prev = { click: false, home: false };

    // braço simplificado: ombro à direita e abaixo da cabeça, antebraço na direção apontada
    const SHOULDER = [0.2, -0.45, -0.05];
    const FOREARM = [0, 0, -0.25];

    // ---------------------------------------------------------------- controles falsos
    const button = () => ({ pressed: false, touched: false, value: 0 });
    const makePad = () => ({
        id: 'DreamLink Daydream',
        index: -1,
        connected: true,
        mapping: 'xr-standard',
        timestamp: 0,
        axes: [0, 0, 0, 0],
        buttons: [button(), button(), button(), button()],
        hapticActuators: [],
        vibrationActuator: null
    });
    const rightSpace = { dreamlink: 'right' };
    const leftSpace = { dreamlink: 'left' };
    const right = {
        handedness: 'right',
        targetRayMode: 'tracked-pointer',
        targetRaySpace: rightSpace,
        gripSpace: null,
        hand: null,
        profiles: [],
        gamepad: makePad()
    };
    // mão esquerda "invisível": só carrega o eixo de andar, que o SuperSplat lê da mão esquerda
    const left = {
        handedness: 'left',
        targetRayMode: 'tracked-pointer',
        targetRaySpace: leftSpace,
        gripSpace: null,
        hand: null,
        profiles: [],
        gamepad: makePad()
    };
    const fakes = [right, left];

    function updatePads(s, frameTime) {
        const active = s.touching && !s.click;
        const dx = active ? s.tx * 2 - 1 : 0;
        const dy = active ? s.ty * 2 - 1 : 0;
        let move = 0;
        let turn = 0;
        if (Math.hypot(dx, dy) > 0.35) {
            if (Math.abs(dy) >= Math.abs(dx)) move = dy; // topo do touch = frente (negativo)
            else turn = dx;
        }
        const rp = right.gamepad;
        const lp = left.gamepad;
        rp.axes[0] = dx;
        rp.axes[1] = dy;
        rp.axes[2] = turn;
        rp.axes[3] = 0;
        lp.axes[2] = 0;
        lp.axes[3] = move;
        rp.buttons[0] = { pressed: s.click, touched: s.click, value: s.click ? 1 : 0 };
        rp.buttons[2] = { pressed: s.click, touched: s.touching, value: s.click ? 1 : 0 };
        rp.timestamp = lp.timestamp = frameTime;
    }

    function controllerPose(w, frame, base) {
        const s = ctl.state;
        if (!s || !ctl.connected) return null;
        const vp = frame.getViewerPose(base);
        if (!vp) return null;
        const hp = vp.transform.position;
        const ho = vp.transform.orientation;
        const headYaw = qYaw([ho.x, ho.y, ho.z, ho.w]);
        const qc = controllerQuat(s.ori);
        if (recenterPending) {
            // O mundo do controle já tem Y para cima (gravidade, conferido com pacotes reais),
            // então o recentro só alinha o giro horizontal; inclinação vem do próprio controle.
            R = qMul(headYaw, qConj(qYaw(qc)));
            recenterPending = false;
        }
        const q = qNorm(qMul(R, qc));
        const sh = qRot(headYaw, SHOULDER);
        const fa = qRot(q, FOREARM);
        const position = { x: hp.x + sh[0] + fa[0], y: hp.y + sh[1] + fa[1], z: hp.z + sh[2] + fa[2], w: 1 };
        const orientation = { x: q[0], y: q[1], z: q[2], w: q[3] };
        const transform = w.XRRigidTransform
            ? new w.XRRigidTransform(position, orientation)
            : { position, orientation };
        return { transform, emulatedPosition: true };
    }

    // ---------------------------------------------------------------- eventos na sessão
    function fire(type, source, frame) {
        const e = new sessionWin.Event(type);
        Object.defineProperty(e, 'inputSource', { value: source });
        Object.defineProperty(e, 'frame', { value: frame });
        session.dispatchEvent(e);
    }

    function fireSourcesChange(added, removed) {
        const e = new sessionWin.Event('inputsourceschange');
        Object.defineProperty(e, 'added', { value: added });
        Object.defineProperty(e, 'removed', { value: removed });
        Object.defineProperty(e, 'session', { value: session });
        session.dispatchEvent(e);
    }

    function onFrame(time, frame) {
        if (ctl.connected && !injected) {
            injected = true;
            recenterPending = true;
            fireSourcesChange(fakes, []);
        } else if (!ctl.connected && injected) {
            if (prev.click) fire('selectend', right, frame);
            prev.click = false;
            injected = false;
            fireSourcesChange([], fakes);
        }
        const s = ctl.state;
        if (!injected || !s) return;

        updatePads(s, time);

        const rc = s.home || s.app; // Home ou App recentralizam
        if (rc && !prev.home) recenterPending = true;
        prev.home = rc;

        if (s.click && !prev.click) {
            fire('selectstart', right, frame);
        } else if (!s.click && prev.click) {
            fire('select', right, frame);
            fire('selectend', right, frame);
        }
        prev.click = s.click;
    }

    function hookSession(w, xrSession) {
        session = xrSession;
        sessionWin = w;
        injected = ctl.connected;
        recenterPending = true;
        prev.click = false;
        prev.home = false;

        const desc = Object.getOwnPropertyDescriptor(w.XRSession.prototype, 'inputSources');
        if (desc && desc.get) {
            Object.defineProperty(xrSession, 'inputSources', {
                configurable: true,
                get() {
                    const list = Array.from(desc.get.call(xrSession));
                    return injected && session === xrSession ? list.concat(fakes) : list;
                }
            });
        }

        const nativeRaf = xrSession.requestAnimationFrame.bind(xrSession);
        xrSession.requestAnimationFrame = (cb) =>
            nativeRaf((time, frame) => {
                try {
                    onFrame(time, frame);
                } catch (err) {
                    console.warn('[DreamLink XR]', err);
                }
                cb(time, frame);
            });

        xrSession.addEventListener('end', () => {
            if (session === xrSession) {
                session = null;
                sessionWin = null;
                injected = false;
            }
        });
    }

    // Instala os ganchos WebXR numa janela (a página ou um quadro do mesmo domínio)
    function hookWindow(w) {
        try {
            if (!w || w.__dreamlinkHooked || !w.XRFrame || !w.XRSystem) return;
            w.__dreamlinkHooked = true;

            const nativeGetPose = w.XRFrame.prototype.getPose;
            w.XRFrame.prototype.getPose = function (space, base) {
                if (space === rightSpace) return controllerPose(w, this, base);
                if (space === leftSpace) return null;
                return nativeGetPose.call(this, space, base);
            };

            const nativeRequest = w.XRSystem.prototype.requestSession;
            w.XRSystem.prototype.requestSession = async function (mode, init) {
                const s = await nativeRequest.call(this, mode, init);
                if (mode === 'immersive-vr') hookSession(w, s);
                return s;
            };

            watchFrames(w);
        } catch {
            // quadro de outro domínio: inacessível, segue sem ele
        }
    }

    function watchFrames(w) {
        const doc = w.document;
        const hookFrame = (f) => {
            const tryHook = () => {
                try {
                    hookWindow(f.contentWindow);
                } catch {
                    /* outro domínio */
                }
            };
            tryHook();
            f.addEventListener('load', tryHook);
        };
        doc.querySelectorAll('iframe').forEach(hookFrame);
        new w.MutationObserver((list) => {
            for (const m of list) {
                m.addedNodes.forEach((n) => {
                    if (n.tagName === 'IFRAME') hookFrame(n);
                    else if (n.querySelectorAll) n.querySelectorAll('iframe').forEach(hookFrame);
                });
            }
        }).observe(doc.documentElement, { childList: true, subtree: true });
    }

    // ---------------------------------------------------------------- Bluetooth
    async function readBattery(server) {
        try {
            const svc = await server.getPrimaryService('battery_service');
            const ch = await svc.getCharacteristic('battery_level');
            const v = await ch.readValue();
            ctl.battery = v.getUint8(0);
        } catch {
            ctl.battery = null;
        }
    }

    async function start(device) {
        setUi('Conectando…');
        const server = await device.gatt.connect();
        const svc = await server.getPrimaryService(SERVICE);
        const ch = await svc.getCharacteristic(DATA_CHAR);
        ch.addEventListener('characteristicvaluechanged', (e) => {
            const s = parse(e.target.value);
            if (s) {
                ctl.state = s;
                ctl.packets++;
            }
        });
        await ch.startNotifications();
        ctl.connected = true;
        recenterPending = true;
        await readBattery(server);
        setUi();
    }

    let retries = 0;
    function onDisconnected() {
        ctl.connected = false;
        ctl.state = null;
        if (!ctl.device || retries >= 20) {
            setUi('Desconectado · toque para conectar');
            return;
        }
        setUi('Reconectando… aperte o Home');
        retries++;
        setTimeout(async () => {
            try {
                await start(ctl.device);
                retries = 0;
            } catch {
                onDisconnected();
            }
        }, 1500);
    }

    async function connect() {
        const nav = root.navigator;
        if (!nav.bluetooth) {
            root.alert('Este navegador não tem Web Bluetooth. Use o Chrome no Android, em página https.');
            return;
        }
        if (ctl.connected) return;
        try {
            const device = await nav.bluetooth.requestDevice({
                filters: [{ namePrefix: 'Daydream' }, { services: [SERVICE] }],
                optionalServices: [SERVICE, 'battery_service']
            });
            ctl.device = device;
            retries = 0;
            device.addEventListener('gattserverdisconnected', onDisconnected);
            await start(device);
        } catch (err) {
            if (err && err.name === 'NotFoundError') setUi('Nenhum controle escolhido');
            else setUi('Falha: ' + (err && err.message ? err.message : err));
        }
    }

    // ---------------------------------------------------------------- interface
    let pill = null;
    function setUi(text) {
        if (!pill) return;
        const dot = pill.firstChild;
        const label = pill.lastChild;
        if (text) {
            label.textContent = text;
            dot.style.background = ctl.connected ? '#4fd1c5' : '#ffb454';
            return;
        }
        if (ctl.connected) {
            const bat = ctl.battery != null ? ' · ' + ctl.battery + '%' : '';
            label.textContent = 'Daydream ' + ctl.pps + ' Hz' + bat;
            dot.style.background = '#4fd1c5';
        } else {
            label.textContent = 'Conectar Daydream';
            dot.style.background = '#8a8f9c';
        }
    }

    function showUi() {
        const doc = root.document;
        if (pill && doc.body.contains(pill)) return;
        pill = doc.createElement('button');
        pill.type = 'button';
        pill.setAttribute('aria-label', 'Conectar controle Daydream');
        pill.style.cssText = [
            'position:fixed', 'top:calc(12px + env(safe-area-inset-top))', 'left:12px', 'z-index:2147483647',
            'display:flex', 'align-items:center', 'gap:8px', 'padding:8px 14px', 'border-radius:999px',
            'border:1px solid rgba(255,255,255,.18)', 'background:rgba(14,15,18,.85)', 'color:#e9eaee',
            'font:600 13px/1.2 system-ui,sans-serif', 'cursor:pointer'
        ].join(';');
        const dot = doc.createElement('i');
        dot.style.cssText = 'width:9px;height:9px;border-radius:50%;display:inline-block;background:#8a8f9c';
        const label = doc.createElement('span');
        label.textContent = 'Conectar Daydream';
        pill.appendChild(dot);
        pill.appendChild(label);
        pill.addEventListener('click', connect);
        doc.body.appendChild(pill);
        setUi();
    }

    setInterval(() => {
        ctl.pps = ctl.packets;
        ctl.packets = 0;
        if (ctl.connected) setUi();
    }, 1000);

    hookWindow(root);
    if (root.document.readyState === 'loading') root.document.addEventListener('DOMContentLoaded', showUi);
    else showUi();

    // ---------------------------------------------------------------- autoteste
    const SAMPLE = [0xd7, 0x08, 0x1d, 0x9c, 0xef, 0x15, 0xf0, 0x3c, 0x82, 0x37,
        0xe8, 0x2f, 0xfc, 0x00, 0x70, 0x01, 0xc0, 0x00, 0x00, 0x01];
    const sample = parse(new DataView(new Uint8Array(SAMPLE).buffer));
    const g = Math.hypot(sample.acc[0], sample.acc[1], sample.acc[2]);
    console.log('[DreamLink XR] parser ' + (g > 9 && g < 11 ? 'OK' : 'DIVERGENTE') + ' · |g| = ' + g.toFixed(2));

    root.dreamlinkXR = {
        connect,
        showUi,
        recenter: () => {
            recenterPending = true;
        },
        get state() {
            return ctl.state;
        },
        get connected() {
            return ctl.connected;
        },
        parse,
        _test: {
            qMul, qRot, qYaw, controllerQuat, updatePads, right, left, hookWindow,
            inject(s, connected = true) {
                ctl.state = s;
                ctl.connected = connected;
            }
        }
    };
})(window);
