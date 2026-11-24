-- Prove2me | Theorems.Thm_ULHC_touch_body
-- name    : ULHC.touch_body
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:53:51.195961+00:00
-- url     : https://prove2.me/theorems/0d8f41f2-8ad6-4a73-a57f-5247e6078bd2
-- title:
--   ULHC: touch body
-- statement:
--   The ULHC construction uses the touch body property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L147-L185
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L147-L185

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
include hpat hz hi0 hi

theorem ULHC.touch_body {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = cellJ c s j) :
    tf = s ∧ i % 2 = j % 2 ∧ i + 1 < m := by sorry
