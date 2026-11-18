// ==UserScript==
// @name         НСПД → НЯК
// @namespace    nspd-to-nyak
// @version      0.5.0
// @description  Сохраняет здания, сооружения и адреса с nspd.gov.ru в CSV и GeoJSON
// @match        https://nspd.gov.ru/*
// @updateURL    https://raw.githubusercontent.com/krumzeze/nspd-to-nyak/main/nspd-to-nyak.user.js
// @downloadURL  https://raw.githubusercontent.com/krumzeze/nspd-to-nyak/main/nspd-to-nyak.user.js
// @run-at       document-start
// @grant        none
// ==/UserScript==

(function () {
  'use strict';

  const API = '/api/geoportal/v1/intersects?typeIntersect=fullObject';
  const R = 6378137;
  const LAYERS = [
    { id: 36369, name: 'Здания', on: true },
    { id: 36383, name: 'Сооружения', on: true },
    { id: 36368, name: 'Участки', on: false },
  ];

  const state = { features: new Map(), withoutNumber: false };

  // ---------- geometry ----------

  function outerRing(geom) {
    if (geom.type === 'Polygon') return geom.coordinates[0];
    if (geom.type === 'MultiPolygon') return geom.coordinates[0][0];
    if (geom.type === 'Point') return [geom.coordinates];
    return null;
  }

  function insideRing(pt, ring) {
    let inside = false;
    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
      const [xi, yi] = ring[i], [xj, yj] = ring[j];
      if ((yi > pt[1]) !== (yj > pt[1]) && pt[0] < ((xj - xi) * (pt[1] - yi)) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  function ringPoint(ring) {
    if (ring.length < 3) return ring[0];
    let a = 0, cx = 0, cy = 0;
    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
      const f = ring[j][0] * ring[i][1] - ring[i][0] * ring[j][1];
      a += f;
      cx += (ring[j][0] + ring[i][0]) * f;
      cy += (ring[j][1] + ring[i][1]) * f;
    }
    const c = a !== 0 ? [cx / (3 * a), cy / (3 * a)] : ring[0];
    if (a !== 0 && insideRing(c, ring)) return c;
    return scanlinePoint(ring, c[1]);
  }

  function scanlinePoint(ring, preferY) {
    const ys = ring.map((p) => p[1]);
    const minY = Math.min(...ys), maxY = Math.max(...ys);
    let best = null;
    for (let k = 0; k <= 20; k++) {
      const y = k === 0 ? preferY : minY + ((maxY - minY) * k) / 21;
      const xs = [];
      for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
        const [xi, yi] = ring[i], [xj, yj] = ring[j];
        if ((yi > y) !== (yj > y)) xs.push(xi + ((y - yi) * (xj - xi)) / (yj - yi));
      }
      xs.sort((p, q) => p - q);
      for (let i = 0; i + 1 < xs.length; i += 2) {
        const w = xs[i + 1] - xs[i];
        if (!best || w > best.w) best = { w, p: [(xs[i] + xs[i + 1]) / 2, y] };
      }
    }
    return best ? best.p : ring[0];
  }

  function toLonLat([x, y]) {
    return [(x / R) * (180 / Math.PI), (2 * Math.atan(Math.exp(y / R)) - Math.PI / 2) * (180 / Math.PI)];
  }

  function geomToLonLat(geom) {
    const conv = (c) => (typeof c[0] === 'number' ? toLonLat(c).map((v) => +v.toFixed(7)) : c.map(conv));
    return { type: geom.type, coordinates: conv(geom.coordinates) };
  }

  // ---------- addresses ----------

  const W = '(?![А-Яа-яЁёA-Za-z])';
  const NUM = '\\d+(?:\\s?[А-Яа-яЁё](?![А-Яа-яЁё.]))?(?:[/-][\\dА-Яа-яЁё]+)*';
  const HOUSE_TOKEN_RE = new RegExp(
    '\\s*(?:' +
      `(?:литера|литер|литреа|лит)${W}\\.?\\s*([А-ЯЁA-Z\\d]{1,3})${W}` +
      `|(?:корпус|корп|к)${W}\\.?\\s*(\\d+[А-Яа-яЁё]?)${W}` +
      `|(?:строение|стр|с)${W}\\.?\\s*(\\d+[А-Яа-яЁё]?)${W}` +
      `|(?:(?:дом|д|зд|здание|двлд|влд|владение|уч-к|уч|участок|з/у|гараж|сооружение|соор)${W}\\.?\\s*)?(?:№\\s*)?(${NUM})(?:\\s*(?:зд|д)\\.?)?` +
    ')\\s*',
    'iy'
  );
  const STREET_RE = new RegExp(
    `^(ул|улица|пер|переулок|пр-кт|проспект|пр-д|проезд|пл|площадь|ш|шоссе|б-р|бульвар|туп|тупик|наб|набережная|мкр|микрорайон|кв-л|квартал|тер|территория|парк|сад|снт|днт|дск|днп|онт|сот|спк|ст|со|с/о|гск|гк|дс|кп|линия|аллея|ряд)${W}`,
    'i'
  );
  const PLACE_RE = new RegExp(
    `^(российская федерация|республика|респ${W}|рт${W}|м\\.р-н|р-н|муниципальный|внутригородское|вн\\.тер|мо${W}|г\\.п|с\\.п|городское|сельское|г${W}|город|с${W}|село|д${W}|деревня|п${W}|пос|поселок|посёлок|рп${W}|пгт${W}|х${W}|хутор|\\d{6})`,
    'i'
  );
  const SETTLEMENT_RE = new RegExp(`^(с|село|д|деревня|п|пос|поселок|посёлок|х|хутор)${W}`, 'i');

  function cleanSpaces(s) {
    return s.replace(/\s+/g, ' ').trim();
  }

  function fullAddress(o) {
    return cleanSpaces(o.readable_address || o.address_readable_address || '');
  }

  function normalizeStreet(s) {
    return cleanSpaces(s.replace(/[«»"“”]/g, ' '));
  }

  function parseHouseSegment(seg, acc) {
    HOUSE_TOKEN_RE.lastIndex = 0;
    const found = {};
    while (HOUSE_TOKEN_RE.lastIndex < seg.length) {
      const m = HOUSE_TOKEN_RE.exec(seg);
      if (!m || m[0] === '') return false;
      if (m[1]) found.lit = m[1];
      if (m[2]) found.korp = m[2];
      if (m[3]) found.str = m[3];
      if (m[4]) found.num = m[4];
    }
    if (found.num && acc.num) return false;
    for (const k in found) if (!acc[k]) acc[k] = found[k];
    return true;
  }

  function formatHouse({ num, korp, str, lit }) {
    let h = num.replace(/\s/g, '').toUpperCase();
    if (/[А-ЯЁ]/.test(h)) h = h.replace(/-/g, '/');
    if (korp) h += 'к' + korp.toUpperCase();
    if (str) h += 'с' + str.toUpperCase();
    if (lit) h += ' лит.' + lit.toUpperCase();
    return h;
  }

  function shortAddress(addr) {
    const parts = addr.replace(/\([^()]*\)/g, ' ').replace(/\.$/, '').split(',').map(cleanSpaces).filter(Boolean);
    const acc = {};
    let hi = parts.length;
    while (hi > 0 && parseHouseSegment(parts[hi - 1], acc)) hi--;
    if (!acc.num && acc.str) { acc.num = acc.str; delete acc.str; }
    if (!acc.num) return null;
    const house = formatHouse(acc);
    let street = null;
    for (let i = hi - 1; i >= 0; i--) {
      const p = parts[i];
      if (STREET_RE.test(p) || (i === hi - 1 && !PLACE_RE.test(p) && !/район|поселение/i.test(p))) {
        street = p;
        break;
      }
    }
    if (!street && hi > 0 && SETTLEMENT_RE.test(parts[hi - 1])) street = parts[hi - 1];
    if (!street) return null;
    return `${house}  ${normalizeStreet(street)}`;
  }

  // ---------- rules ----------

  const RULES_KEY = 'nspdToNyak.rules.v2';
  const OLD_RULES_KEY = 'nspdToNyak.rulesText';
  const DEFAULT_RULES = `# Правила обработки адреса перед разбором на номер дома и улицу.
# Применяются сверху вниз. Полный адрес в CSV остаётся как в реестре.
#
#   что заменить => на что заменить        простая замена
#   " с пробелами " => ", "                 кавычки сохраняют пробелы по краям
#   re: шаблон => замена                    регулярное выражение, $1 или \\1 — группа
#   re/i: шаблон => замена                  то же без учёта регистра
#   пропустить: текст                       выкинуть объект, если в адресе есть текст
#   пропустить re: шаблон                   выкинуть, если адрес подходит под шаблон
#   пропустить без: текст                   выкинуть, если текста в адресе нет
#   пропустить без re: шаблон               выкинуть, если адрес не подходит под шаблон

re/i: \\bулица\\b => ул
re/i: \\bпереулок\\b => пер
re/i: \\bпроспект\\b => пр-кт
re/i: \\bплощадь\\b => пл
re/i: \\bпроезд\\b => пр-д
re/i: \\b(?:тер\\.?|территория) +(?=\\S) => ""
re/i: \\bдачно-садоводческое и огородническое (?:некоммерческое )?то+варищество\\b => ДС и ОНТ
re/i: \\bсадоводческое некомм?ерческое товарищество\\b => СНТ
re/i: \\bсадоводческий потребительский кооператив\\b => СПК
re/i: \\bсадовое товарищество\\b => СТ
re/i: (?:\\bсадоводческое товарищество\\b|\\bсадов\\.\\s*тов\\.|\\bс/т\\.?)(?= ) => СТ
re/i: (?:\\bсадоводческое общество\\b|\\bс/о\\b) => СО
re/i: \\bДСиОНТ\\b => ДС и ОНТ
re/i: \\b(СНТ|ДНТ|СТ|СО|СПК)\\.? +\\1\\b\\.? => $1
re/i: \\b(СНТ|ДНТ|СПК)\\. => $1
re: \\bснт\\b => СНТ
`;

  const WORD = '[\\p{L}\\p{N}_]';
  const UNICODE_B = `(?:(?<=${WORD})(?!${WORD})|(?<!${WORD})(?=${WORD}))`;

  function unquote(v) {
    const m = v.match(/^"(.*)"$/s);
    return m ? m[1] : v;
  }

  function compileRe(pattern, flags) {
    if (/\\b/.test(pattern)) return new RegExp(pattern.replace(/\\b/g, UNICODE_B), flags + 'u');
    return new RegExp(pattern, flags);
  }

  function parseRules(text) {
    const rules = [], errors = [];
    text.replace(/^﻿/, '').split(/\r?\n/).forEach((line, i) => {
      if (!line.trim() || line.trim().startsWith('#')) return;
      try {
        let m;
        if ((m = line.match(/^\s*пропустить( без)?( re)?:\s?(.*)$/i))) {
          const neg = !!m[1], value = unquote(m[3]);
          if (!value) throw new Error('пустое условие');
          const re = m[2] ? compileRe(value, '') : null;
          const has = re ? (s) => re.test(s) : (s) => s.includes(value);
          rules.push({ skip: neg ? (s) => !has(s) : has });
        } else if ((m = line.match(/^\s*re(\/i)?:\s?(.*?) => ?(.*)$/i))) {
          const to = unquote(m[3]).replace(/\$/g, '$$$$').replace(/\\(\d)/g, '$$$1').replace(/\$\$(\d)/g, '$$$1');
          rules.push({ re: compileRe(unquote(m[2]), m[1] ? 'gi' : 'g'), to });
        } else if ((m = line.match(/^("[^"]*"|.*?)(?: ?=> ?|\t|;)("[^"]*"|.*)$/)) && unquote(m[1])) {
          rules.push({ from: unquote(m[1]), to: unquote(m[2]) });
        } else {
          throw new Error('не понял правило');
        }
      } catch (e) {
        errors.push(`Строка ${i + 1}: ${e.message}`);
      }
    });
    return { rules, errors };
  }

  function processAddress(s, rules = state.rules.rules) {
    for (const r of rules) {
      if (r.skip) { if (r.skip(s)) return null; }
      else if (r.re) s = s.replace(r.re, r.to);
      else s = s.split(r.from).join(r.to);
    }
    return s;
  }

  function addressRow(raw, rules) {
    const processed = processAddress(raw, rules);
    if (processed == null) return { skipped: true };
    return { short: shortAddress(cleanSpaces(processed)) };
  }

  function setRulesText(text) {
    state.rules = { text, ...parseRules(text) };
    try { localStorage.setItem(RULES_KEY, text); } catch (e) { /* ignore */ }
    renderRules();
    render();
  }

  state.rules = (() => {
    let text = DEFAULT_RULES;
    try {
      const saved = localStorage.getItem(RULES_KEY);
      const old = localStorage.getItem(OLD_RULES_KEY);
      if (saved != null) text = saved;
      else if (old && parseRules(old).rules.length) text = DEFAULT_RULES + '\n# Ваши правила из прошлой версии\n' + old;
    } catch (e) { /* ignore */ }
    return { text, ...parseRules(text) };
  })();

  function previewSamples(limit) {
    const cats = new Set(LAYERS.filter((l) => l.on).map((l) => l.id));
    const out = [];
    for (const f of state.features.values()) {
      if (!cats.has(f.properties.category)) continue;
      const raw = fullAddress(f.properties.options || {});
      if (!raw) continue;
      out.push(raw);
      if (out.length >= limit) break;
    }
    return out;
  }

  function openRulesEditor() {
    const overlay = document.createElement('div');
    overlay.style.cssText = 'position:fixed;inset:0;z-index:2147483647;background:rgba(0,0,0,.4);display:flex;align-items:center;justify-content:center;font:13px sans-serif;color:#222';
    const box = document.createElement('div');
    box.style.cssText = 'width:min(900px,94vw);max-height:90vh;display:flex;flex-direction:column;gap:8px;padding:14px;background:#fff;border-radius:10px;box-shadow:0 4px 24px rgba(0,0,0,.3)';

    const title = document.createElement('div');
    title.style.cssText = 'font-weight:bold;font-size:15px';
    title.textContent = 'Правила обработки адресов';

    const hint = document.createElement('div');
    hint.style.color = '#555';
    hint.textContent = 'Правила применяются сверху вниз, подсказка по формату в начале списка. Справа видно, что получится с адресами из текущей выборки.';

    const cols = document.createElement('div');
    cols.style.cssText = 'display:flex;gap:10px;min-height:0;flex:1';

    const area = document.createElement('textarea');
    area.value = state.rules.text;
    area.spellcheck = false;
    area.wrap = 'off';
    area.style.cssText = 'flex:1;min-height:320px;padding:8px;border:1px solid #bbb;border-radius:6px;font:13px monospace;resize:vertical';

    const preview = document.createElement('div');
    preview.style.cssText = 'flex:1;min-height:320px;max-height:60vh;overflow:auto;padding:8px;border:1px solid #eee;border-radius:6px;background:#fafafa;font-size:12px';

    const samples = previewSamples(60);
    function updatePreview() {
      const { rules, errors } = parseRules(area.value);
      preview.textContent = '';
      for (const e of errors) {
        const d = document.createElement('div');
        d.style.cssText = 'color:#c62828;font-weight:bold;padding:2px 0';
        d.textContent = e;
        preview.append(d);
      }
      if (!samples.length) {
        preview.append('Сначала выделите объекты на карте, тогда здесь появятся примеры.');
        return;
      }
      for (const raw of samples) {
        const res = addressRow(raw, rules);
        const row = document.createElement('div');
        row.style.cssText = 'padding:4px 0;border-bottom:1px solid #eee';
        const a = document.createElement('div');
        a.style.cssText = 'white-space:pre;font-weight:bold';
        if (res.skipped) { a.textContent = '— пропущен правилом —'; a.style.color = '#c62828'; }
        else if (!res.short) { a.textContent = '— не нашёл номер дома —'; a.style.color = '#b26a00'; }
        else a.textContent = res.short;
        const b = document.createElement('div');
        b.style.color = '#777';
        b.textContent = raw;
        row.append(a, b);
        preview.append(row);
      }
    }
    area.oninput = updatePreview;
    updatePreview();

    const actions = document.createElement('div');
    actions.style.cssText = 'display:flex;gap:8px;flex-wrap:wrap';
    const act = (text, onClick, primary) => {
      const b = button(text, onClick);
      b.style.width = 'auto';
      b.style.padding = '6px 12px';
      if (primary) { b.style.background = '#2f6fdf'; b.style.color = '#fff'; }
      return b;
    };
    const close = () => overlay.remove();
    actions.append(
      act('Сохранить', () => {
        if (parseRules(area.value).errors.length && !confirm('В правилах есть ошибки, такие строки будут пропущены. Сохранить?')) return;
        setRulesText(area.value);
        close();
      }, true),
      act('Отмена', close),
      act('Вернуть стандартные', () => {
        if (confirm('Заменить текущие правила стандартными?')) { area.value = DEFAULT_RULES; updatePreview(); }
      }),
      act('Загрузить из файла…', () => {
        const input = document.createElement('input');
        input.type = 'file';
        input.accept = '.txt,.csv,text/plain';
        input.onchange = async () => {
          if (!input.files[0]) return;
          area.value = await input.files[0].text();
          updatePreview();
        };
        input.click();
      }),
      act('Сохранить в файл', () => download('правила.txt', area.value, 'text/plain;charset=utf-8')),
    );

    cols.append(area, preview);
    box.append(title, hint, cols, actions);
    overlay.append(box);
    overlay.onclick = (e) => { if (e.target === overlay) close(); };
    document.body.append(overlay);
    area.focus();
  }

  // ---------- collection ----------

  function addFeatures(fc) {
    let added = 0;
    for (const f of fc.features || []) {
      if (!f.geometry || !f.properties) continue;
      const key = f.id ?? f.properties.externalKey;
      if (!state.features.has(key)) added++;
      state.features.set(key, f);
    }
    render(added);
  }

  function selectedRows() {
    const cats = new Set(LAYERS.filter((l) => l.on).map((l) => l.id));
    const rows = [];
    for (const f of state.features.values()) {
      if (!cats.has(f.properties.category)) continue;
      const o = f.properties.options || {};
      const raw = fullAddress(o);
      const res = raw ? addressRow(raw) : { short: null };
      if (res.skipped || (!res.short && !state.withoutNumber)) continue;
      const ring = outerRing(f.geometry);
      if (!ring) continue;
      const [lon, lat] = toLonLat(ringPoint(ring));
      rows.push({ f, o, lat, lon, full: raw, short: res.short });
    }
    return rows;
  }

  // ---------- export ----------

  function download(name, text, type) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(new Blob([text], { type }));
    a.download = name;
    document.body.appendChild(a);
    a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  }

  function csv(rows, pick) {
    return rows.map((r) => `${r.lat};${r.lon};;${pick(r).replace(/[;\r\n]/g, ' ')}`).join('\r\n') + '\r\n';
  }

  function exportFullCsv() {
    download('Reestr_all.csv', csv(selectedRows(), (r) => r.full), 'text/csv;charset=utf-8');
  }

  function exportShortCsv() {
    download('Reestr_oks.csv', csv(selectedRows(), (r) => r.short || r.full), 'text/csv;charset=utf-8');
  }

  function exportGeoJson() {
    const fc = {
      type: 'FeatureCollection',
      features: selectedRows().map((r) => ({
        type: 'Feature',
        geometry: geomToLonLat(r.f.geometry),
        properties: {
          cad_num: r.f.properties.externalKey || r.o.cad_num || r.o.cad_number || '',
          category: r.f.properties.categoryName,
          address: r.full,
          short_address: r.short || '',
          purpose: r.o.purpose || r.o.params_purpose || r.o.land_record_category_type || '',
          floors: r.o.floors || r.o.params_floors || '',
          lat: r.lat,
          lon: r.lon,
        },
      })),
    };
    download('R_OKS.geojson', JSON.stringify(fc), 'application/geo+json');
  }

  // ---------- network ----------

  function isIntersects(url) {
    return typeof url === 'string' && url.includes('/intersects') && url.includes('fullObject');
  }

  const origFetch = window.fetch;
  window.fetch = async function (input, init) {
    const res = await origFetch.apply(this, arguments);
    try {
      const url = typeof input === 'string' ? input : input && input.url;
      if (isIntersects(url) && res.ok) res.clone().json().then(addFeatures).catch(() => {});
    } catch (e) { /* ignore */ }
    return res;
  };

  const origOpen = XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open = function (method, url) {
    if (isIntersects(String(url))) {
      this.addEventListener('load', () => {
        try {
          const data = this.responseType === 'json' ? this.response : JSON.parse(this.responseText);
          addFeatures(data);
        } catch (e) { /* ignore */ }
      });
    }
    return origOpen.apply(this, arguments);
  };

  function screenPolygon() {
    const p = new URLSearchParams(location.search);
    const x = parseFloat(p.get('coordinate_x')), y = parseFloat(p.get('coordinate_y')), z = parseFloat(p.get('zoom'));
    if (!isFinite(x) || !isFinite(y) || !isFinite(z)) return null;
    const canvas = [...document.querySelectorAll('canvas')].sort((a, b) => b.clientWidth * b.clientHeight - a.clientWidth * a.clientHeight)[0];
    const w = canvas ? canvas.clientWidth : window.innerWidth;
    const h = canvas ? canvas.clientHeight : window.innerHeight;
    const res = 156543.03392804097 / Math.pow(2, z);
    const dx = (w / 2) * res, dy = (h / 2) * res;
    return [[x - dx, y + dy], [x + dx, y + dy], [x + dx, y - dy], [x - dx, y - dy], [x - dx, y + dy]];
  }

  async function fetchScreen() {
    const poly = screenPolygon();
    if (!poly) {
      setStatus('Не удалось определить экран. Обведите область инструментом выделения на карте.');
      return;
    }
    const cats = LAYERS.filter((l) => l.on).map((l) => ({ id: l.id }));
    if (!cats.length) { setStatus('Отметьте хотя бы один слой.'); return; }
    setStatus('Загружаю…');
    const body = {
      geom: { type: 'FeatureCollection', features: [{ type: 'Feature', properties: {}, geometry: { type: 'Polygon', coordinates: [poly], crs: { type: 'name', properties: { name: 'EPSG:3857' } } } }] },
      categories: cats,
    };
    try {
      const res = await origFetch(API, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) });
      if (!res.ok) throw new Error('HTTP ' + res.status);
      addFeatures(await res.json());
    } catch (e) {
      setStatus('Ошибка загрузки: ' + e.message);
    }
  }

  // ---------- UI ----------

  let panel, statusEl, rulesEl;

  function renderRules() {
    if (!rulesEl) return;
    const { rules, errors } = state.rules;
    rulesEl.textContent = `Правил обработки: ${rules.length}` + (errors.length ? `, с ошибками: ${errors.length}` : '');
  }

  function setStatus(text) {
    if (statusEl) statusEl.textContent = text;
  }

  function render(added) {
    if (!panel) return;
    const counts = {};
    for (const f of state.features.values()) counts[f.properties.category] = (counts[f.properties.category] || 0) + 1;
    const rows = selectedRows();
    const parts = LAYERS.map((l) => `${l.name}: ${counts[l.id] || 0}`).join(', ');
    setStatus(`${added != null ? `Добавлено ${added}. ` : ''}Всего: ${parts}. В выгрузку попадёт: ${rows.length}`);
  }

  function button(text, onClick) {
    const b = document.createElement('button');
    b.textContent = text;
    b.style.cssText = 'display:block;width:100%;margin:4px 0;padding:6px;border:1px solid #2f6fdf;border-radius:6px;background:#fff;color:#2f6fdf;cursor:pointer;font:13px sans-serif';
    b.onclick = onClick;
    return b;
  }

  function checkbox(label, checked, onChange) {
    const l = document.createElement('label');
    l.style.cssText = 'display:block;margin:2px 0;cursor:pointer';
    const c = document.createElement('input');
    c.type = 'checkbox';
    c.checked = checked;
    c.style.marginRight = '6px';
    c.onchange = () => { onChange(c.checked); render(); };
    l.append(c, label);
    return l;
  }

  function buildPanel() {
    panel = document.createElement('div');
    panel.style.cssText = 'position:fixed;left:12px;bottom:12px;z-index:2147483647;width:240px;padding:10px;background:#fff;border-radius:10px;box-shadow:0 2px 12px rgba(0,0,0,.25);font:13px sans-serif;color:#222';

    const head = document.createElement('div');
    head.style.cssText = 'display:flex;justify-content:space-between;align-items:center;font-weight:bold;margin-bottom:6px;cursor:pointer';
    head.textContent = 'НСПД → НЯК';
    const toggle = document.createElement('span');
    toggle.textContent = '–';
    head.append(toggle);

    const body = document.createElement('div');
    head.onclick = () => {
      const hidden = body.style.display === 'none';
      body.style.display = hidden ? '' : 'none';
      toggle.textContent = hidden ? '–' : '+';
    };

    for (const l of LAYERS) body.append(checkbox(l.name, l.on, (v) => { l.on = v; }));
    body.append(checkbox('Без номера дома тоже', state.withoutNumber, (v) => { state.withoutNumber = v; }));

    body.append(
      button('Взять весь экран', fetchScreen),
      button('Скачать CSV (полный адрес)', exportFullCsv),
      button('Скачать CSV (короткий адрес)', exportShortCsv),
      button('Скачать GeoJSON', exportGeoJson),
      button('Очистить', () => { state.features.clear(); render(); }),
    );

    rulesEl = document.createElement('div');
    rulesEl.style.cssText = 'margin-top:8px;font-size:12px';
    body.append(
      rulesEl,
      button('Правила обработки…', openRulesEditor),
    );
    renderRules();

    statusEl = document.createElement('div');
    statusEl.style.cssText = 'margin-top:6px;color:#555;font-size:12px';
    statusEl.textContent = 'Обведите область на карте или нажмите «Взять весь экран».';
    body.append(statusEl);

    panel.append(head, body);
    document.body.append(panel);
  }

  if (document.body) buildPanel();
  else document.addEventListener('DOMContentLoaded', buildPanel);

  window.__nspdToNyak = { shortAddress, ringPoint, toLonLat, outerRing, parseRules, processAddress, addressRow, DEFAULT_RULES, state };
})();
