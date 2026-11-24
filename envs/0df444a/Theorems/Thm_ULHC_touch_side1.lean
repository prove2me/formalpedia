-- Prove2me | Theorems.Thm_ULHC_touch_side1
-- name    : ULHC.touch_side1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:54:00.99297+00:00
-- url     : https://prove2.me/theorems/2f4e165c-0288-4d2f-88f3-29ca035c9fbf
-- title:
--   ULHC: touch side1
-- statement:
--   The ULHC construction uses the touch side1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L440-L462
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L440-L462

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

theorem ULHC.touch_side1 {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by sorry
