const TRMAP={'ı':'i','ş':'s','ğ':'g','ü':'u','ö':'o','ç':'c'};
function normName(s){
  s=String(s).replace(/İ/g,'i').replace(/I/g,'ı').toLowerCase();
  s=s.replace(/[ışğüöç]/g,function(c){return TRMAP[c];});
  return s.replace(/[^a-z0-9]/g,'');
}
function makeMatcher(str,emptyAll){
  var toks=String(str||'').split(/[,;]/).map(normName).filter(Boolean);
  if(!toks.length) return emptyAll?function(){return true;}:function(){return false;};
  var vars=[];
  toks.forEach(function(t){vars.push(t);if(t.length>4&&t.charAt(t.length-1)==='i')vars.push(t.slice(0,-1));});
  return function(name){var n=normName(name);for(var i=0;i<vars.length;i++){if(n.indexOf(vars[i])>=0)return true;}return false;};
}
function cleanText(s,mtext){
  s=String(s||'').replace(/\\U\+([0-9A-Fa-f]{4})/g,function(m,h){return String.fromCharCode(parseInt(h,16));});
  if(mtext){
    s=s.replace(/\\P/g,' ').replace(/\\~/g,' ').replace(/\\[ACcFfHhQqTtWw][^;]*;/g,'').replace(/\\[LlOoKk]/g,'').replace(/[{}]/g,'').replace(/\\\\/g,'\\');
  }
  return s.replace(/%%[cC]/g,'Ø').replace(/%%[dD]/g,'°').replace(/%%[pP]/g,'±').replace(/\s+/g,' ').trim();
}
function bulgeSeg(p0,p1,b,pts){
  var dx=p1.x-p0.x,dy=p1.y-p0.y,c=Math.hypot(dx,dy);
  if(!b||c===0){pts.push({x:p1.x,y:p1.y});return c;}
  var th=4*Math.atan(b),h=c/2,s=Math.sin(th/2),r=Math.abs(h/s),off=h/Math.tan(th/2);
  var cx=(p0.x+p1.x)/2+(-dy/c)*off,cy=(p0.y+p1.y)/2+(dx/c)*off;
  var a0=Math.atan2(p0.y-cy,p0.x-cx),n=Math.max(2,Math.ceil(Math.abs(th)/(Math.PI/18)));
  for(var i=1;i<=n;i++){var a=a0+th*i/n;pts.push({x:cx+r*Math.cos(a),y:cy+r*Math.sin(a)});}
  return r*Math.abs(th);
}
function polyGeom(v,closed){
  if(v.length<2)return null;
  var pts=[{x:v[0].x,y:v[0].y}],len=0;
  for(var i=0;i<v.length-1;i++)len+=bulgeSeg(v[i],v[i+1],v[i].b,pts);
  if(closed&&v.length>2)len+=bulgeSeg(v[v.length-1],v[0],v[v.length-1].b,pts);
  return {pts:pts,len:len};
}
function ptsLen(pts){var l=0;for(var i=0;i<pts.length-1;i++)l+=Math.hypot(pts[i+1].x-pts[i].x,pts[i+1].y-pts[i].y);return l;}
function distPtSeg(px,py,a,b){
  var dx=b.x-a.x,dy=b.y-a.y,l2=dx*dx+dy*dy,t=l2?((px-a.x)*dx+(py-a.y)*dy)/l2:0;
  t=Math.max(0,Math.min(1,t));return Math.hypot(px-(a.x+t*dx),py-(a.y+t*dy));
}
function distPtPoly(px,py,pts){
  if(pts.length===1)return Math.hypot(px-pts[0].x,py-pts[0].y);
  var m=Infinity;for(var i=0;i<pts.length-1;i++){var d=distPtSeg(px,py,pts[i],pts[i+1]);if(d<m)m=d;}return m;
}
function arcPts(cx,cy,r,a0,sw){
  var n=Math.max(8,Math.ceil(Math.abs(sw)/(Math.PI/24))),pts=[];
  for(var i=0;i<=n;i++){var a=a0+sw*i/n;pts.push({x:cx+r*Math.cos(a),y:cy+r*Math.sin(a)});}
  return pts;
}
function DxfParser(opts){
  this.layerMatch=opts.layerMatch||function(){return false;};
  this.textMatch=opts.textMatch||function(){return false;};
  this.sec=null;this.expectSec=false;this.hdrVar=null;this.cur=null;this.poly=null;
  this.lines=[];this.texts=[];this.textByHandle=new Map();this.leaders=[];
  this.layerCounts={};this.insunits=null;this.unsup=0;this.inserts=0;this.nEnt=0;this.approx=0;
}
DxfParser.prototype.feed=function(code,val){
  if(code===0){
    if(val==='SECTION'){this.expectSec=true;return;}
    if(val==='ENDSEC'){this.flush();if(this.poly){this.finalize(this.poly);this.poly=null;}this.sec=null;return;}
    if(val==='EOF'){return;}
    if(this.sec==='ENTITIES'){this.flush();this.begin(val);}
    return;
  }
  if(this.expectSec&&code===2){this.sec=val;this.expectSec=false;return;}
  if(this.sec==='HEADER'){
    if(code===9)this.hdrVar=val;
    else if(this.hdrVar==='$INSUNITS'&&code===70){this.insunits=parseInt(val,10);this.hdrVar=null;}
    return;
  }
  if(this.sec==='ENTITIES'&&this.cur)this.accum(code,val);
};
DxfParser.prototype.begin=function(t){
  if(this.poly&&t!=='VERTEX'&&t!=='SEQEND'){this.finalize(this.poly);this.poly=null;}
  if(t==='SEQEND'){if(this.poly){this.finalize(this.poly);this.poly=null;}this.cur=null;return;}
  if(t==='VERTEX'){this.cur={t:t,parent:this.poly,vtx:{x:0,y:0,b:0,f:0}};return;}
  var e={t:t,layer:'0',handle:'',v:[],flags:0};
  if(t==='POLYLINE')this.poly=e;
  if(t==='SPLINE'){e.fit=[];}
  if(t==='MTEXT'){e.chunks=[];}
  if(t==='MULTILEADER'){e.inLL=false;e.text='';}
  this.cur=e;
};
DxfParser.prototype.flush=function(){
  var e=this.cur;if(!e)return;this.cur=null;
  if(e.t==='POLYLINE')return;
  if(e.t==='VERTEX'){var vt=e.vtx;if(e.parent&&!(vt.f&16)&&!(vt.f&128))e.parent.v.push({x:vt.x,y:vt.y,b:vt.b});return;}
  this.finalize(e);
};
DxfParser.prototype.accum=function(code,val){
  var e=this.cur,t=e.t;
  if(t==='VERTEX'){
    var vt=e.vtx;
    if(code===10)vt.x=parseFloat(val);else if(code===20)vt.y=parseFloat(val);
    else if(code===42)vt.b=parseFloat(val);else if(code===70)vt.f=parseInt(val,10)||0;
    return;
  }
  if(code===8){e.layer=val;return;}
  if(code===5){e.handle=val;return;}
  var f=parseFloat(val),last;
  switch(t){
    case 'LINE':
      if(code===10)e.x1=f;else if(code===20)e.y1=f;else if(code===11)e.x2=f;else if(code===21)e.y2=f;break;
    case 'LWPOLYLINE':
      if(code===70)e.flags=parseInt(val,10)||0;
      else if(code===10)e.v.push({x:f,y:0,b:0});
      else if(code===20&&e.v.length)e.v[e.v.length-1].y=f;
      else if(code===42&&e.v.length)e.v[e.v.length-1].b=f;break;
    case 'POLYLINE':
      if(code===70)e.flags=parseInt(val,10)||0;break;
    case 'ARC':
      if(code===10)e.cx=f;else if(code===20)e.cy=f;else if(code===40)e.r=f;else if(code===50)e.a0=f;else if(code===51)e.a1=f;break;
    case 'CIRCLE':
      if(code===10)e.cx=f;else if(code===20)e.cy=f;else if(code===40)e.r=f;break;
    case 'SPLINE':
      if(code===70)e.flags=parseInt(val,10)||0;
      else if(code===10)e.v.push({x:f,y:0});
      else if(code===20&&e.v.length)e.v[e.v.length-1].y=f;
      else if(code===11)e.fit.push({x:f,y:0});
      else if(code===21&&e.fit.length)e.fit[e.fit.length-1].y=f;break;
    case 'ELLIPSE':
      if(code===10)e.cx=f;else if(code===20)e.cy=f;else if(code===11)e.mx=f;else if(code===21)e.my=f;
      else if(code===40)e.ratio=f;else if(code===41)e.p0=f;else if(code===42)e.p1=f;break;
    case 'TEXT':
      if(code===10)e.x1=f;else if(code===20)e.y1=f;else if(code===11){e.x2=f;e.has11=true;}else if(code===21)e.y2=f;
      else if(code===72||code===73){if(parseInt(val,10)>0)e.al=true;}
      else if(code===1)e.text=val;break;
    case 'MTEXT':
      if(code===10)e.x1=f;else if(code===20)e.y1=f;else if(code===3)e.chunks.push(val);else if(code===1)e.text=val;break;
    case 'LEADER':
      if(code===10)e.v.push({x:f,y:0});
      else if(code===20&&e.v.length)e.v[e.v.length-1].y=f;
      else if(code===340)e.annot=val;break;
    case 'MULTILEADER':
      if(code===304){
        if(/\{$/.test(val))e.inLL=true;else e.text=val;
      }else if(code===305||code===303){if(val==='}')e.inLL=false;}
      else if(code===12){e.lx=f;e.hasLoc=true;}
      else if(code===22)e.ly=f;
      else if(code===10&&e.inLL)e.v.push({x:f,y:0});
      else if(code===20&&e.inLL&&e.v.length)e.v[e.v.length-1].y=f;break;
  }
};
DxfParser.prototype.geomOf=function(e){
  var pts,i,n;
  switch(e.t){
    case 'LINE':
      if(!isFinite(e.x1+e.y1+e.x2+e.y2))return null;
      return {pts:[{x:e.x1,y:e.y1},{x:e.x2,y:e.y2}],len:Math.hypot(e.x2-e.x1,e.y2-e.y1)};
    case 'LWPOLYLINE':return polyGeom(e.v,(e.flags&1)===1);
    case 'POLYLINE':if(e.flags&(16|64))return 'unsup';return polyGeom(e.v,(e.flags&1)===1);
    case 'ARC':{
      var a0=e.a0*Math.PI/180,a1=e.a1*Math.PI/180;if(a1<=a0)a1+=2*Math.PI;
      pts=arcPts(e.cx,e.cy,e.r,a0,a1-a0);return {pts:pts,len:e.r*(a1-a0)};
    }
    case 'CIRCLE':
      pts=arcPts(e.cx,e.cy,e.r,0,2*Math.PI);return {pts:pts,len:2*Math.PI*e.r};
    case 'SPLINE':{
      var src=e.fit.length>=2?e.fit:e.v;if(src.length<2)return null;
      pts=src.map(function(p){return {x:p.x,y:p.y};});
      if(e.flags&1)pts.push({x:pts[0].x,y:pts[0].y});
      return {pts:pts,len:ptsLen(pts),approx:true};
    }
    case 'ELLIPSE':{
      var p0=e.p0||0,p1=(e.p1===undefined?2*Math.PI:e.p1);if(p1<=p0)p1+=2*Math.PI;
      var ux=e.mx,uy=e.my,vx=-uy*e.ratio,vy=ux*e.ratio;pts=[];n=96;
      for(i=0;i<=n;i++){var a=p0+(p1-p0)*i/n;pts.push({x:e.cx+ux*Math.cos(a)+vx*Math.sin(a),y:e.cy+uy*Math.cos(a)+vy*Math.sin(a)});}
      return {pts:pts,len:ptsLen(pts),approx:true};
    }
  }
  return null;
};
DxfParser.prototype.finalize=function(e){
  var L=e.layer||'0';
  this.nEnt++;this.layerCounts[L]=(this.layerCounts[L]||0)+1;
  if(e.t==='TEXT'||e.t==='MTEXT'){
    var raw=e.t==='MTEXT'?(e.chunks.join('')+(e.text||'')):(e.text||'');
    var text=cleanText(raw,e.t==='MTEXT');
    if(!text)return;
    var pos=(e.t==='TEXT'&&e.has11&&e.al)?{x:e.x2,y:e.y2}:{x:e.x1,y:e.y1};
    if(!isFinite(pos.x+pos.y))return;
    var rec={text:text,pos:pos,layer:L,handle:e.handle};
    if(e.handle)this.textByHandle.set(e.handle,rec);
    if(this.textMatch(L))this.texts.push(rec);
  }else if(e.t==='LEADER'||e.t==='MULTILEADER'){
    this.leaders.push(e);
  }else if(e.t==='INSERT'){
    if(this.layerMatch(L))this.inserts++;
  }else if(this.layerMatch(L)){
    var g=this.geomOf(e);
    if(g==='unsup')this.unsup++;
    else if(g&&g.len>0&&isFinite(g.len)){
      if(g.approx)this.approx++;
      this.lines.push({layer:L,type:e.t,len:g.len,pts:g.pts,label:null,handle:e.handle});
    }
  }
};
function nearestText(cands,x,y){
  var best=null,bd=Infinity;
  for(var i=0;i<cands.length;i++){var d=Math.hypot(cands[i].pos.x-x,cands[i].pos.y-y);if(d<bd){bd=d;best=cands[i];}}
  return {t:best,d:bd};
}
function buildResult(P,opts){
  var maxDist=opts.maxDist>0?opts.maxDist:Infinity,used={},marks=[],lines=P.lines,i,j;
  for(i=0;i<P.leaders.length;i++){
    var ld=P.leaders[i];if(!ld.v.length)continue;
    var label=null,tpos=null;
    if(ld.t==='LEADER'){
      var th=ld.annot&&P.textByHandle.get(ld.annot);
      if(th){label=th.text;tpos=th.pos;used[ld.annot]=true;}
    }else{
      label=cleanText(ld.text||'',true);if(ld.hasLoc)tpos={x:ld.lx,y:ld.ly};
    }
    var tip=ld.v[0],tail=ld.v[ld.v.length-1];
    if(tpos){var far=-1;for(j=0;j<ld.v.length;j++){var dd=Math.hypot(ld.v[j].x-tpos.x,ld.v[j].y-tpos.y);if(dd>far){far=dd;tip=ld.v[j];}}tail=tpos;}
    if(!label){
      var nt=nearestText(P.texts,tail.x,tail.y);
      if(nt.t){label=nt.t.text;if(nt.t.handle)used[nt.t.handle]=true;}
    }
    var best=null,bd=Infinity;
    for(j=0;j<lines.length;j++){var d=distPtPoly(tip.x,tip.y,lines[j].pts);if(d<bd){bd=d;best=lines[j];}}
    if(best&&label){best.label=label;best.dist=bd;best.via='leader';best.far=bd>maxDist;}
    marks.push({tip:tip,tail:tail,label:label,ok:!!(best&&label)});
  }
  var cand=P.texts.filter(function(t){return !(t.handle&&used[t.handle]);});
  for(i=0;i<lines.length;i++){
    var L=lines[i];if(L.label)continue;
    var bt=null,bdist=Infinity;
    for(j=0;j<cand.length;j++){var dd2=distPtPoly(cand[j].pos.x,cand[j].pos.y,L.pts);if(dd2<bdist){bdist=dd2;bt=cand[j];}}
    if(bt){L.label=bt.text;L.dist=bdist;L.via='text';L.far=bdist>maxDist;}
  }
  var map=new Map(),layerTotals={},total=0;
  for(i=0;i<lines.length;i++){
    var Ln=lines[i],lab=Ln.label?Ln.label.replace(/\s+/g,' ').trim():'';
    var key=lab?lab.toLocaleUpperCase('tr'):'';
    var g=map.get(key);
    if(!g){g={label:lab||'(Etiketsiz)',key:key,count:0,total:0,lines:[],far:0};map.set(key,g);}
    g.count++;g.total+=Ln.len;g.lines.push(Ln);if(Ln.far)g.far++;
    layerTotals[Ln.layer]=layerTotals[Ln.layer]||{count:0,total:0};
    layerTotals[Ln.layer].count++;layerTotals[Ln.layer].total+=Ln.len;
    total+=Ln.len;
  }
  var groups=Array.from(map.values()).sort(function(a,b){
    if(!a.key&&b.key)return 1;if(a.key&&!b.key)return -1;
    return a.label.localeCompare(b.label,'tr',{numeric:true});
  });
  return {groups:groups,total:total,layerTotals:layerTotals,marks:marks,count:lines.length,
    unlabeled:groups.filter(function(g){return !g.key;}).reduce(function(s,g){return s+g.count;},0),
    far:groups.reduce(function(s,g){return s+g.far;},0)};
}
function katOf(l){
  var m=/\bkat\s*[:\-.]?\s*(-?\d+)/i.exec(l)||/(-?\d+)\s*\.?\s*kat\b/i.exec(l)||/(?:^|[^a-z0-9])k\s*[-:]?\s*(\d+)(?![a-z0-9])/i.exec(l);
  return m?String(parseInt(m[1],10)):null;
}
var UNIT_CM={cm:1,mm:0.1,m:100};
var lastUnit='cm';
function unitFromIns(n){return n===4?'mm':n===5?'cm':n===6?'m':null;}

var $=function(id){return document.getElementById(id);};
var fileObj=null,lastRes=null,lastP=null,lastFactor=1,view=null;
var fmt=function(n,d){return n.toLocaleString('tr-TR',{maximumFractionDigits:d===undefined?2:d});};
function esc(s){return String(s).replace(/[&<>"]/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c];});}
function setBar(p){var b=$('bar');b.style.display=p<0?'none':'block';b.firstElementChild.style.width=(p<0?0:p)+'%';}
function showMsg(id,cls,html){$(id).innerHTML=html?'<div class="msg '+cls+'">'+html+'</div>':'';}

async function readFile(file,parser,onProg){
  var head=new Uint8Array(await file.slice(0,262144).arrayBuffer());
  var hs=new TextDecoder('latin1').decode(head);
  if(hs.indexOf('AutoCAD Binary DXF')===0)throw new Error('BIN');
  var enc='utf-8',ver=/\$ACADVER\s*\r?\n\s*1\s*\r?\n\s*(AC\d+)/.exec(hs);
  if(!(ver&&ver[1]>='AC1021')){
    var cp=/\$DWGCODEPAGE\s*\r?\n\s*3\s*\r?\n\s*([^\r\n]+)/.exec(hs);
    cp=cp?cp[1].trim().toUpperCase():'';
    if(cp==='ANSI_1254')enc='windows-1254';
    else if(cp==='ANSI_1252')enc='windows-1252';
    else if(cp==='ANSI_1251')enc='windows-1251';
    else if(cp==='ANSI_1250')enc='windows-1250';
    else if(ver)enc='windows-1254';
  }
  var dec;try{dec=new TextDecoder(enc);}catch(e){dec=new TextDecoder('utf-8');}
  var CH=4*1024*1024,off=0,carry='',pend=null,size=file.size;
  while(off<size){
    var buf=await file.slice(off,off+CH).arrayBuffer();off+=CH;
    var txt=carry+dec.decode(new Uint8Array(buf),{stream:off<size});
    var arr=txt.split('\n');carry=arr.pop();
    for(var i=0;i<arr.length;i++){
      var ln=arr[i];
      if(pend===null){var c=parseInt(ln,10);if(!isNaN(c))pend=c;}
      else{parser.feed(pend,ln.replace(/\r$/,'').trim());pend=null;}
    }
    onProg&&onProg(Math.min(100,off/size*100));
    await new Promise(function(r){setTimeout(r,0);});
  }
  if(carry&&pend!==null)parser.feed(pend,carry.replace(/\r$/,'').trim());
  parser.flush();if(parser.poly){parser.finalize(parser.poly);parser.poly=null;}
}
function pickFile(f){
  if(!f)return;
  fileObj=f;$('fname').textContent=f.name+' · '+fmt(f.size/1048576,2)+' MB';
  $('go').disabled=true;$('res').classList.add('hide');showMsg('runMsg','','');showMsg('fileMsg','','');
  $('layerBox').classList.add('hide');setBar(0);
  var P=new DxfParser({});
  readFile(f,P,setBar).then(function(){
    setBar(-1);
    var n=Object.keys(P.layerCounts).length;
    if(!n){showMsg('fileMsg','err','Bu dosyada çizim (ENTITIES) bulunamadı. DXF dosyasının ASCII formatında kaydedildiğinden emin olun.');return;}
    lastP0=P;renderChips(P);
    var u=unitFromIns(P.insunits);
    showMsg('fileMsg','info','Dosya okundu: '+fmt(P.nEnt,0)+' nesne, '+n+' layer.'+(u?' Dosya birimi: <b>'+u+'</b>.':' Dosyada birim bilgisi yok; birimi aşağıdan seçebilirsiniz (otomatikte cm kabul edilir).'));
    $('go').disabled=false;
  }).catch(function(e){
    setBar(-1);
    showMsg('fileMsg','err',e&&e.message==='BIN'?'Bu bir ikili (binary) DXF. Lütfen ASCII DXF olarak kaydedin (AutoCAD: SAVEAS → DXF → Seçenekler → ASCII).':'Dosya okunamadı: '+esc(e&&e.message||e));
  });
}
var lastP0=null;
function renderChips(P){
  var ent=Object.entries(P.layerCounts).sort(function(a,b){return b[1]-a[1];});
  var ch=$('chips');ch.innerHTML='';
  ent.forEach(function(kv){
    var s=document.createElement('span');s.className='chip';s.innerHTML=esc(kv[0])+'<i>'+fmt(kv[1],0)+'</i>';
    s.onclick=function(){toggleLayer(kv[0]);syncChips();};
    s.dataset.l=kv[0];ch.appendChild(s);
  });
  $('layerBox').classList.remove('hide');syncChips();
}
function toggleLayer(name){
  var parts=$('layers').value.split(/[,;]/).map(function(s){return s.trim();}).filter(Boolean);
  var idx=parts.findIndex(function(p){return normName(p)===normName(name);});
  if(idx>=0)parts.splice(idx,1);else parts.push(name);
  $('layers').value=parts.join(', ');
}
function syncChips(){
  var m=makeMatcher($('layers').value);
  document.querySelectorAll('#chips .chip').forEach(function(c){c.classList.toggle('on',m(c.dataset.l));});
}
$('layers').addEventListener('input',syncChips);
var drop=$('drop'),inp=$('file');
drop.addEventListener('click',function(){inp.click();});
inp.addEventListener('change',function(){pickFile(inp.files[0]);});
$('go').addEventListener('click',function(){
  if(!fileObj)return;
  var lstr=$('layers').value.trim();
  if(!lstr){showMsg('runMsg','err','En az bir layer adı yazın.');return;}
  showMsg('runMsg','','');$('go').disabled=true;$('go').textContent='Hesaplanıyor…';
  var P=new DxfParser({layerMatch:makeMatcher(lstr),textMatch:makeMatcher($('tlayers').value,true)});
  readFile(fileObj,P,setBar).then(function(){
    setBar(-1);
    var u=$('unit').value;
    if(u==='auto'){u=unitFromIns(P.insunits)||'cm';}
    var factor=UNIT_CM[u];
    var res=buildResult(P,{maxDist:parseFloat($('maxd').value)});
    lastRes=res;lastP=P;lastFactor=factor;lastUnit=u;
    renderResult(res,P,u);
  }).catch(function(e){
    setBar(-1);showMsg('runMsg','err',e&&e.message==='BIN'?'İkili DXF desteklenmiyor, ASCII DXF kaydedin.':'Hesaplama hatası: '+esc(e&&e.message||e));
  }).then(function(){$('go').disabled=false;$('go').textContent='Metrajı hesapla';});
});
function row(cells,cls){return '<tr'+(cls?' class="'+cls+'"':'')+'>'+cells.join('')+'</tr>';}
function renderResult(res,P,unit){
  var f=lastFactor,cm=function(v){return v*f;};
  $('res').classList.remove('hide');
  if(!res.count){
    $('big').innerHTML='';$('tbl').innerHTML='';$('katWrap').classList.add('hide');$('lwrap').classList.add('hide');
    $('warns').innerHTML='<div class="msg warn">Yazdığınız layer adlarına uyan çizgi bulunamadı. Yukarıdaki layer listesinden dokunarak seçebilirsiniz.</div>';
    drawPreview(res,P);return;
  }
  $('big').innerHTML='<div class="k"><small>Toplam uzunluk</small><b>'+fmt(res.total)+' <em>'+lastUnit+'</em></b></div>'+
    '<div class="k"><small>Toplam (metre)</small><b>'+fmt(cm(res.total)/100,3)+' <em>m</em></b></div>'+
    '<div class="k"><small>Çizgi / mahal</small><b>'+fmt(res.count,0)+' <em>/ '+res.groups.filter(function(g){return g.key;}).length+'</em></b></div>';
  var w=[];
  if(res.unlabeled)w.push('<b>'+res.unlabeled+'</b> çizgiye mahal yazısı eşleşmedi (tabloda "Etiketsiz"). Mahal yazısı layer adını ve yazıların çizgilere yakınlığını kontrol edin.');
  if(res.far)w.push('<b>'+res.far+'</b> çizgide yazı belirlediğiniz uyarı mesafesinden uzak (⚠). Yanlış yazı eşleşmiş olabilir, önizlemeden kontrol edin.');
  if(P.inserts)w.push('Seçili layer\'larda <b>'+P.inserts+'</b> blok (INSERT) var, blok içi çizgiler sayılmadı. Patlatıp (explode) tekrar deneyin.');
  if(P.approx)w.push('<b>'+P.approx+'</b> spline/elips yaklaşık hesaplandı.');
  if(P.unsup)w.push('<b>'+P.unsup+'</b> 3B/ağ polyline desteklenmiyor, atlandı.');
  w.push('Birim: <b>'+unit+'</b>'+($('unit').value==='auto'&&!unitFromIns(P.insunits)?' (dosyada birim yok, cm varsayıldı)':'')+'.');
  $('warns').innerHTML=w.map(function(x,i){return '<div class="msg '+(i===w.length-1?'info':'warn')+'">'+x+'</div>';}).join('');
  var h='<tr><th>Mahal</th><th class="n">Çizgi</th><th class="n">'+lastUnit+'</th><th class="n">m</th></tr>';
  res.groups.forEach(function(g){
    h+=row(['<td>'+esc(g.label)+'</td>','<td class="n">'+g.count+'</td>','<td class="n">'+fmt(g.total)+'</td>','<td class="n">'+fmt(cm(g.total)/100,3)+'</td>'],(g.far?'far ':'')+(g.key?'':'nolabel'));
  });
  h+=row(['<td>Genel toplam</td>','<td class="n">'+res.count+'</td>','<td class="n">'+fmt(res.total)+'</td>','<td class="n">'+fmt(cm(res.total)/100,3)+'</td>'],'sum');
  $('tbl').innerHTML=h;
  $('katWrap').classList.add('hide');
  var lk=Object.keys(res.layerTotals);
  if(lk.length>1){
    var lh='<tr><th>Layer</th><th class="n">Çizgi</th><th class="n">'+lastUnit+'</th><th class="n">m</th></tr>';
    lk.sort().forEach(function(k){var o=res.layerTotals[k];lh+=row(['<td>'+esc(k)+'</td>','<td class="n">'+o.count+'</td>','<td class="n">'+fmt(o.total)+'</td>','<td class="n">'+fmt(cm(o.total)/100,3)+'</td>']);});
    $('ltbl').innerHTML=lh;$('lwrap').classList.remove('hide');
  }else $('lwrap').classList.add('hide');
  drawPreview(res,P);
}
var PAL=['#12b5d6','#e07a1f','#7a3fd0','#10a566','#d6336c','#c9a227','#2b6cb0','#8a5a2b','#0f766e','#6b7280'];
function fitView(res,P){
  var minx=Infinity,miny=Infinity,maxx=-Infinity,maxy=-Infinity;
  P.lines.forEach(function(L){L.pts.forEach(function(p){if(p.x<minx)minx=p.x;if(p.x>maxx)maxx=p.x;if(p.y<miny)miny=p.y;if(p.y>maxy)maxy=p.y;});});
  res.marks.forEach(function(m){[m.tip,m.tail].forEach(function(p){if(p){if(p.x<minx)minx=p.x;if(p.x>maxx)maxx=p.x;if(p.y<miny)miny=p.y;if(p.y>maxy)maxy=p.y;}});});
  P.texts.forEach(function(t){if(t.pos.x<minx)minx=t.pos.x;if(t.pos.x>maxx)maxx=t.pos.x;if(t.pos.y<miny)miny=t.pos.y;if(t.pos.y>maxy)maxy=t.pos.y;});
  if(!isFinite(minx))return null;
  var cv=$('cv'),w=cv.clientWidth,h=cv.clientHeight,pad=28;
  var sx=(w-2*pad)/Math.max(maxx-minx,1e-9),sy=(h-2*pad)/Math.max(maxy-miny,1e-9),s=Math.min(sx,sy);
  if(!isFinite(s)||s<=0)s=1;
  return {s:s,ox:w/2-(minx+maxx)/2*s,oy:h/2+(miny+maxy)/2*s};
}
function drawPreview(res,P){
  if(!view||view.res!==res)view=null;
  var f=fitView(res,P);
  if(!view&&f)view={res:res,P:P,s:f.s,ox:f.ox,oy:f.oy,fit:f};
  paint();
}
function paint(){
  var cv=$('cv'),dpr=window.devicePixelRatio||1,w=cv.clientWidth,h=cv.clientHeight;
  cv.width=w*dpr;cv.height=h*dpr;
  var ctx=cv.getContext('2d');ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,w,h);
  if(!view){ctx.fillStyle='#5f6f87';ctx.font='14px sans-serif';ctx.fillText('Gösterilecek çizgi yok',14,26);return;}
  var res=view.res,P=view.P,s=view.s,ox=view.ox,oy=view.oy;
  var X=function(x){return x*s+ox;},Y=function(y){return oy-y*s;};
  var colorOf={};res.groups.forEach(function(g,i){colorOf[g.key]=g.key?PAL[i%PAL.length]:'#d12a2a';});
  ctx.lineJoin='round';ctx.lineCap='round';
  P.texts.forEach(function(t){ctx.fillStyle='#9aa8bd';ctx.beginPath();ctx.arc(X(t.pos.x),Y(t.pos.y),2.5,0,7);ctx.fill();});
  res.groups.forEach(function(g){
    ctx.strokeStyle=colorOf[g.key];ctx.lineWidth=3;
    g.lines.forEach(function(L){
      ctx.beginPath();L.pts.forEach(function(p,i){if(i)ctx.lineTo(X(p.x),Y(p.y));else ctx.moveTo(X(p.x),Y(p.y));});ctx.stroke();
    });
  });
  ctx.font='600 12px sans-serif';ctx.textBaseline='middle';
  res.groups.forEach(function(g){
    ctx.fillStyle=colorOf[g.key];
    g.lines.forEach(function(L){
      var p=L.pts[Math.floor(L.pts.length/2)],tx=X(p.x)+6,ty=Y(p.y)-12;
      var lab=g.label;ctx.lineWidth=3;ctx.strokeStyle='#fff';ctx.strokeText(lab,tx,ty);ctx.fillText(lab,tx,ty);
    });
  });
  res.marks.forEach(function(m){
    ctx.strokeStyle=m.ok?'#555':'#d12a2a';ctx.fillStyle=ctx.strokeStyle;ctx.lineWidth=1.2;ctx.setLineDash([4,3]);
    ctx.beginPath();ctx.moveTo(X(m.tail.x),Y(m.tail.y));ctx.lineTo(X(m.tip.x),Y(m.tip.y));ctx.stroke();ctx.setLineDash([]);
    ctx.beginPath();ctx.arc(X(m.tip.x),Y(m.tip.y),4,0,7);ctx.fill();
  });
}

/* ---- kopyala, kat özeti, yakınlaştırma ---- */
function katOf(label){
  var m=/(\d+)\s*\.?\s*kat\b/i.exec(label)||/\bkat\s*[-:]?\s*(\d+)/i.exec(label)||/(?:^|[^a-z0-9])k\s*(\d+)(?![a-z0-9])/i.exec(label);
  return m?m[1]+'. Kat':null;
}
function katGroups(){
  if(!lastRes||!$('bykat').checked)return null;
  var o={},order=[];
  lastRes.groups.forEach(function(g){
    var k=katOf(g.label)||'Kat belirtilmemiş';
    if(!o[k]){o[k]={count:0,total:0};order.push(k);}
    o[k].count+=g.count;o[k].total+=g.total;
  });
  order.sort(function(a,b){return (parseInt(a)||999)-(parseInt(b)||999);});
  return {o:o,order:order};
}
function renderKat(){
  var K=katGroups(),f=lastFactor;
  if(!K){$('katWrap').classList.add('hide');return;}
  var h='<tr><th>Kat</th><th class="n">Çizgi</th><th class="n">'+lastUnit+'</th><th class="n">m</th></tr>';
  K.order.forEach(function(k){var x=K.o[k];h+=row(['<td>'+esc(k)+'</td>','<td class="n">'+x.count+'</td>','<td class="n">'+fmt(x.total)+'</td>','<td class="n">'+fmt(x.total*f/100,3)+'</td>']);});
  $('ktbl').innerHTML=h;$('katWrap').classList.remove('hide');
}
$('bykat').addEventListener('change',renderKat);
var _rr=renderResult;
renderResult=function(res,P,unit){_rr(res,P,unit);renderKat();};

function num(v,d){return v.toFixed(d).replace('.',',');}
function buildCopyText(){
  if(!lastRes||!lastRes.count)return '';
  var f=lastFactor,L=['Mahal\tÇizgi\t'+lastUnit+'\tm'];
  lastRes.groups.forEach(function(g){L.push([g.label,g.count,num(g.total,2),num(g.total*f/100,3)].join('\t'));});
  L.push(['Genel toplam',lastRes.count,num(lastRes.total,2),num(lastRes.total*f/100,3)].join('\t'));
  var K=katGroups();
  if(K){L.push('');L.push('Kat\tÇizgi\t'+lastUnit+'\tm');K.order.forEach(function(k){var x=K.o[k];L.push([k,x.count,num(x.total,2),num(x.total*f/100,3)].join('\t'));});}
  return L.join('\n');
}
function fallbackCopy(txt){
  var ta=$('cp');ta.style.display='block';ta.value=txt;ta.focus();ta.select();
  try{ta.setSelectionRange(0,txt.length);}catch(e){}
  var ok=false;try{ok=document.execCommand('copy');}catch(e){}
  return ok;
}
$('copy').addEventListener('click',function(){
  var txt=buildCopyText(),btn=$('copy'),old="Sonucu kopyala (Excel'e yapıştırılır)";
  if(!txt){btn.textContent='Kopyalanacak sonuç yok';setTimeout(function(){btn.textContent=old;},1800);return;}
  function done(ok){
    if(ok){btn.textContent='Kopyalandı ✓';$('cp').style.display='none';}
    else{btn.textContent='Aşağıdaki metni seçip kopyalayın';}
    setTimeout(function(){btn.textContent=old;},2200);
  }
  // iOS/Android'de en güvenilir yol: kullanıcı dokunuşu içinde eşzamanlı kopyalama
  var ok=fallbackCopy(txt);
  if(ok){done(true);return;}
  if(navigator.clipboard&&navigator.clipboard.writeText){
    navigator.clipboard.writeText(txt).then(function(){done(true);},function(){done(false);});
  }else done(false);
});

function zoomAt(k,cx,cy){
  if(!view)return;
  var cv=$('cv');if(cx==null){cx=cv.clientWidth/2;cy=cv.clientHeight/2;}
  var wx=(cx-view.ox)/view.s,wy=(view.oy-cy)/view.s;
  view.s*=k;view.ox=cx-wx*view.s;view.oy=cy+wy*view.s;paint();
}
$('zi').addEventListener('click',function(){zoomAt(1.4);});
$('zo').addEventListener('click',function(){zoomAt(1/1.4);});
$('zf').addEventListener('click',function(){if(view&&view.fit){view.s=view.fit.s;view.ox=view.fit.ox;view.oy=view.fit.oy;paint();}});
(function(){
  var cv=$('cv'),pts={},lastD=0,lastC=null;
  cv.style.touchAction='none';
  function pos(e){var r=cv.getBoundingClientRect();return {x:e.clientX-r.left,y:e.clientY-r.top};}
  cv.addEventListener('pointerdown',function(e){pts[e.pointerId]=pos(e);try{cv.setPointerCapture(e.pointerId);}catch(x){}lastD=0;lastC=null;});
  cv.addEventListener('pointermove',function(e){
    if(!view||!pts[e.pointerId])return;
    var p=pos(e),ids=Object.keys(pts);
    if(ids.length>=2){
      pts[e.pointerId]=p;
      var a=pts[ids[0]],b=pts[ids[1]],d=Math.hypot(a.x-b.x,a.y-b.y),c={x:(a.x+b.x)/2,y:(a.y+b.y)/2};
      if(lastD)zoomAt(d/lastD,c.x,c.y);
      if(lastC){view.ox+=c.x-lastC.x;view.oy+=c.y-lastC.y;paint();}
      lastD=d;lastC=c;
    }else{
      var o=pts[e.pointerId];view.ox+=p.x-o.x;view.oy+=p.y-o.y;pts[e.pointerId]=p;paint();
    }
  });
  function up(e){delete pts[e.pointerId];lastD=0;lastC=null;}
  cv.addEventListener('pointerup',up);cv.addEventListener('pointercancel',up);
  cv.addEventListener('wheel',function(e){e.preventDefault();var p=pos(e);zoomAt(e.deltaY<0?1.15:1/1.15,p.x,p.y);},{passive:false});
  window.addEventListener('resize',function(){if(view)paint();});
})();
