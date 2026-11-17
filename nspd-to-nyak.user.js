// ==UserScript==
// @name         НСПД → НЯК
// @namespace    nspd-to-nyak
// @version      0.2.0
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
  const ABBR = [
    [/^улица(?=\s)/i, 'ул'],
    [/^переулок(?=\s)/i, 'пер'],
    [/^проспект(?=\s)/i, 'пр-кт'],
    [/^площадь(?=\s)/i, 'пл'],
    [/^проезд(?=\s)/i, 'пр-д'],
    [/^(?:тер\.?|территория)\s+(?=\S)/i, ''],
    [/^дачно-садоводческое и огородническое (?:некоммерческое )?то+варищество/i, 'ДС и ОНТ'],
    [/^садоводческое некомм?ерческое товарищество/i, 'СНТ'],
    [/^садоводческий потребительский кооператив/i, 'СПК'],
    [/^(?:садоводческое товарищество|садов\.\s*тов\.|с\/т\.?)(?=\s)/i, 'СТ'],
    [/^(?:садоводческое общество|с\/о)/i, 'СО'],
    [/^ДСиОНТ/i, 'ДС и ОНТ'],
    [/^(СНТ|ДНТ|СТ|СО|СПК|ДС и ОНТ)\.?\s+(?:\1\.?\s+)?/i, (m, t) => t.toUpperCase().replace('ДС И ОНТ', 'ДС и ОНТ') + ' '],
  ];
  const SETTLEMENT_RE = new RegExp(`^(с|село|д|деревня|п|пос|поселок|посёлок|х|хутор)${W}`, 'i');

  function cleanSpaces(s) {
    return s.replace(/\s+/g, ' ').trim();
  }

  function fullAddress(o) {
    return cleanSpaces(o.readable_address || o.address_readable_address || '');
  }

  function normalizeStreet(s) {
    s = cleanSpaces(s.replace(/[«»"“”]/g, ' '));
    for (const [re, to] of ABBR) s = cleanSpaces(s.replace(re, to));
    return s;
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
      const full = fullAddress(o);
      const short = full ? shortAddress(full) : null;
      if (!short && !state.withoutNumber) continue;
      const ring = outerRing(f.geometry);
      if (!ring) continue;
      const [lon, lat] = toLonLat(ringPoint(ring));
      rows.push({ f, o, lat, lon, full, short });
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

  let panel, statusEl;

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

    statusEl = document.createElement('div');
    statusEl.style.cssText = 'margin-top:6px;color:#555;font-size:12px';
    statusEl.textContent = 'Обведите область на карте или нажмите «Взять весь экран».';
    body.append(statusEl);

    panel.append(head, body);
    document.body.append(panel);
  }

  if (document.body) buildPanel();
  else document.addEventListener('DOMContentLoaded', buildPanel);

  window.__nspdToNyak = { shortAddress, ringPoint, toLonLat, outerRing };
})();
