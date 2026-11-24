-- Prove2me | Theorems.Thm_ULHC_touch_side2
-- name    : ULHC.touch_side2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:54:17.742834+00:00
-- url     : https://prove2.me/theorems/d0223ad7-a356-41fb-a61e-a734a10c683c
-- title:
--   ULHC: touch side2
-- statement:
--   The ULHC construction uses the touch side2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L465-L487
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L465-L487

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hT hk hcell hpat hsep hz hi0 hi

theorem ULHC.touch_side2 {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by sorry
