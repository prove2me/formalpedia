-- Prove2me | Theorems.Thm_ULHC_start_beyond
-- name    : ULHC.start_beyond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:53.694722+00:00
-- url     : https://prove2.me/theorems/d7a483c6-9c88-4d53-8734-83a155d647d0
-- title:
--   ULHC: start beyond
-- statement:
--   The ULHC construction uses the start beyond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L452-L499
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L452-L499

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)
include hF hT hk hcell hpat hsep hb hxd hxlat hxl hxu hdu

theorem ULHC.start_beyond (_hs : Solid V) (x0 : Pt) (_hconn : ∀ z ∈ V, Conn (GE V) x0 z)
    (hT' : NoTypeIII V (flipCol F c s (k + 2))) {m : ℕ} (hfr : front d tf ∈ F ↔ m = 1)
    (hd : d = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ front d tf ∉ F) ∨
      (m = 1 ∧ u = nb d s ∧ lat1 d s ∈ F ∧ lat2 d s ∈ F ∧ front d s ∈ F) := by sorry
