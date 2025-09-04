local bit=require("bit")
local log,pi,sin,sqrt,abs,max,min,floor,ceil=math.log,math.pi,math.sin,math.sqrt,math.abs,math.max,math.min,math.floor,math.ceil

local Notes={}
Notes.offsets={C=-9,["C#"]=-8,Db=-8,D=-7,["D#"]=-6,Eb=-6,E=-5,F=-4,["F#"]=-3,Gb=-3,G=-2,["G#"]=-1,Ab=-1,A=0,["A#"]=1,Bb=1,B=2}
function Notes.log2(x) return log(x)/log(2) end
function Notes.freq(note) local n,oct=note:match("^([A-G][#b]?)(%d+)$"); assert(n and oct,"bad note:"..tostring(note)); local o=tonumber(oct); local off=assert(Notes.offsets[n],"bad name:"..n); return 440.0*(2^((off+(o-4)*12)/12.0)) end
function Notes.split(s) local t={} for w in s:gmatch("([^%s]+)") do t[#t+1]=w end; return t end
function Notes.tofreqs(s) local r={} for _,k in ipairs(Notes.split(s)) do r[#r+1]=Notes.freq(k) end; return r end

local WAV={}
local function u16le(n) local lo=bit.band(n,0xff); local hi=bit.band(bit.rshift(n,8),0xff); return string.char(lo,hi) end
local function u32le(n) local b0=bit.band(n,0xff); local b1=bit.band(bit.rshift(n,8),0xff); local b2=bit.band(bit.rshift(n,16),0xff); local b3=bit.band(bit.rshift(n,24),0xff); return string.char(b0,b1,b2,b3) end
function WAV.write_mono16(path,sr,framestr)
  local data_size=#framestr; local fmt_size=16; local riff_size=4+(8+fmt_size)+(8+data_size)
  local f=assert(io.open(path,"wb"))
  f:write("RIFF",u32le(riff_size),"WAVE","fmt ",u32le(fmt_size),u16le(1),u16le(1),u32le(sr),u32le(sr*2),u16le(2),u16le(16),"data",u32le(data_size),framestr)
  f:close()
end

local Phys={}
function Phys.rk4_step(x,v,om,ze,dt,a)
  for i=1,#x do
    local xi,vi,wi,zi=x[i],v[i],om[i],ze[i]
    local function acc(px,pv) return -(2.0*zi*wi)*pv-(wi*wi)*px-a*(px*px*px) end
    local k1x=dt*vi;             local k1v=dt*acc(xi,vi)
    local k2x=dt*(vi+0.5*k1v);   local k2v=dt*acc(xi+0.5*k1x,vi+0.5*k1v)
    local k3x=dt*(vi+0.5*k2v);   local k3v=dt*acc(xi+0.5*k2x,vi+0.5*k2v)
    local k4x=dt*(vi+k3v);       local k4v=dt*acc(xi+k3x,vi+k3v)
    x[i]=xi+(k1x+2*k2x+2*k3x+k4x)/6.0; v[i]=vi+(k1v+2*k2v+2*k3v+k4v)/6.0
  end
end

local GuitarString={}
GuitarString.__index=GuitarString
function GuitarString:new(f_open,cfg)
  local o=setmetatable({},self); cfg=cfg or {}
  o.f_open=f_open; o.m=cfg.num_modes or 8; o.inharm=cfg.inharm or 3e-4; o.db=cfg.damp_base or 8e-4; o.ds=cfg.damp_slope or 5e-4; o.alpha=cfg.alpha or 0.0
  o.x={}; o.v={}; o.om={}; o.ze={}
  for i=1,o.m do o.x[i]=0.0; o.v[i]=0.0; o.om[i]=0.0; o.ze[i]=0.0 end
  o:set_fret(0); return o
end
function GuitarString:set_fret(fret)
  local f1=self.f_open*(2^(fret/12.0))
  for k=1,self.m do local fk=f1*k*sqrt(1.0+self.inharm*(k*k)); self.om[k]=2.0*pi*fk; self.ze[k]=self.db+self.ds*k end
end
function GuitarString:excite(fret,vel,ppos)
  vel=vel or 1.0; ppos=ppos or 0.2
  for i=1,self.m do self.x[i]=0.0; self.v[i]=0.0 end
  self:set_fret(fret)
  local norm=0.0; local w={}
  for k=1,self.m do local wk=sin(pi*k*ppos)/k; w[k]=wk; norm=norm+abs(wk) end
  if norm<1e-12 then norm=1.0 end
  for i=1,self.m do self.v[i]=self.v[i]+vel*(w[i]/norm) end
end
function GuitarString:step(dt) Phys.rk4_step(self.x,self.v,self.om,self.ze,dt,self.alpha) end
function GuitarString:sample() local s=0.0; for i=1,self.m do s=s+self.x[i] end; return s end

local Guitar={}
function Guitar.new(open_freqs,cfg) local t={} for i=1,#open_freqs do t[i]=GuitarString:new(open_freqs[i],cfg) end; return {strings=t,type="guitar",open=open_freqs} end
local function choose_string_and_fret(open,target,max_fret)
  max_fret=max_fret or 20
  local best,b_s,b_f=nil,nil,nil
  for s_idx,f_open in ipairs(open) do
    local ideal=12.0*Notes.log2(target/f_open); local fret=floor(ideal+0.5)
    if fret>=0 and fret<=max_fret then
      local pitched=f_open*(2^(fret/12.0)); local cents=abs(1200.0*Notes.log2(pitched/target))
      local score=fret<0 and -fret or fret; local a=score; local b=cents
      if not best or a<best[1] or (a==best[1] and b<best[2]) then best={a,b}; b_s=s_idx; b_f=fret end
    end
  end
  if b_s then return b_s,b_f end
  local best_r=1e309
  for s_idx,f_open in ipairs(open) do
    local ideal=12.0*Notes.log2(target/f_open); local fret=floor(ideal+0.5)
    if fret<0 then fret=0 elseif fret>max_fret then fret=max_fret end
    local pitched=f_open*(2^(fret/12.0)); local r=abs(Notes.log2(pitched/target))
    if r<best_r then best_r=r; b_s=s_idx; b_f=fret end
  end
  return b_s,b_f
end

local Arrange={}
function Arrange.parse_melody(toks) local r={} for i=1,#toks do local a,b,vel,pp=toks[i]:match("^([^:]+):([^:@]+)@?([^#]*)#?(.*)$"); if not a then error("bad token:"..toks[i]) end; r[#r+1]={a,tonumber(b),vel~="" and tonumber(vel) or 1.0,pp~="" and tonumber(pp) or nil} end; return r end
function Arrange.melody_to_events(open,melody,bpm)
  local beat=60.0/(bpm or 100); local t=0.0; local ev={}; local denom=max(1,#open-1)
  for i=1,#melody do
    local token,beats,vel,pp=melody[i][1],melody[i][2],melody[i][3],melody[i][4]; local dur=beats*beat
    if token:upper()=="R" then t=t+dur else
      local f=Notes.freq(token); local s_idx,fret=choose_string_and_fret(open,f)
      local ppos=pp or (0.18+0.04*((s_idx-1)/denom))
      ev[#ev+1]={t,s_idx,fret,vel,ppos}; t=t+dur
    end
  end
  return ev,t+2.0
end

local Engine={}
function Engine.render(song,outpath)
  local sr=song.sample_rate or 44100
  local tracks=song.tracks
  local events_by_sample,strings={},{}
  local total_dur=0.0
  for ti=1,#tracks do
    local tr=tracks[ti]
    if tr.instrument.type=="guitar" then
      local open=tr.instrument.open
      local ev,dur=Arrange.melody_to_events(open,tr.melody,tr.bpm or song.bpm); if dur>total_dur then total_dur=dur end
      local t2s={}
      for _,e in ipairs(ev) do local idx=max(0,min(floor(e[1]*sr),floor(dur*sr)-1)); local row=events_by_sample[idx] or {}; row[#row+1]={ti,e}; events_by_sample[idx]=row end
      strings[ti]=tr.instrument.strings
    else error("unknown instrument") end
  end
  local dt=1.0/sr; local total_samples=floor(total_dur*sr+0.5); local active={}
  for i=1,#tracks do local n=#(strings[i] or {}); active[i]={}; for j=1,n do active[i][j]=false end end
  local out={} out[total_samples]=0.0
  for n=0,total_samples-1 do
    local trig=events_by_sample[n]
    if trig then for j=1,#trig do local ti,e=trig[j][1],trig[j][2]; local sidx,fret,vel,ppos=e[2],e[3],e[4],e[5]; strings[ti][sidx]:excite(fret,vel,ppos); active[ti][sidx]=true end end
    local s=0.0
    for ti=1,#tracks do if strings[ti] then for si=1,#strings[ti] do if active[ti][si] then strings[ti][si]:step(dt); s=s+strings[ti][si]:sample()*(tracks[ti].gain or 1.0) end end end end
    out[n+1]=s*(song.master_gain or 0.8)
  end
  local peak=1e-12; for i=1,#out do local a=abs(out[i]); if a>peak then peak=a end end
  local gain=(0.9*32767.0)/peak; local bytes={}
  for i=1,#out do local v=out[i]*gain; if v>=0 then v=floor(v+0.5) else v=ceil(v-0.5) end; if v<-32768 then v=-32768 elseif v>32767 then v=32767 end; if v<0 then v=v+65536 end; bytes[#bytes+1]=u16le(v) end
  WAV.write_mono16(outpath or (song.title or "song")..".wav",sr,table.concat(bytes))
end

local Presets={}
function Presets.standard_guitar(cfg) return Guitar.new(Notes.tofreqs("E2 A2 D3 G3 B3 E4"),cfg) end
function Presets.drop_d(cfg) return Guitar.new(Notes.tofreqs("D2 A2 D3 G3 B3 E4"),cfg) end

local function make_song_ducks()
  local DUCKS={
    "C4:1","D4:1","E4:1","F4:1","G4:2",
    "A4:2","G4:2","F4:2","E4:2",
    "G4:2","F4:2","E4:2","D4:2","C4:4",
  }
  local guitar=Presets.standard_guitar()
  return {
    title="guitar_ducks", bpm=96, sample_rate=44100, master_gain=0.8,
    tracks={
      {instrument=guitar, melody=Arrange.parse_melody(DUCKS), gain=1.0},
    }
  }
end

local song=make_song_ducks()
Engine.render(song,(song.title or "song")..".wav")
print("done:",song.title)
