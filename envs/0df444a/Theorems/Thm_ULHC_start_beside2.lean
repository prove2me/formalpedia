-- Prove2me | Theorems.Thm_ULHC_start_beside2
-- name    : ULHC.start_beside2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:01:42.84021+00:00
-- url     : https://prove2.me/theorems/21f41c6f-ae45-4a8e-a0fc-989a9f598547
-- title:
--   ULHC: start beside2
-- statement:
--   The ULHC construction uses the start beside2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L313-L367
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L313-L367

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
include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu

theorem ULHC.start_beside2 {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat2 d s := by sorry
