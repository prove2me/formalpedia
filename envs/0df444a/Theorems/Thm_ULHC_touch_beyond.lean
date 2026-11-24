-- Prove2me | Theorems.Thm_ULHC_touch_beyond
-- name    : ULHC.touch_beyond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:26:24.583318+00:00
-- url     : https://prove2.me/theorems/e219e571-0356-43cd-80a9-f9a9c8d94298
-- title:
--   ULHC: touch beyond
-- statement:
--   The ULHC construction uses the touch beyond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L331-L403
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L331-L403

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
include hF hk hpat hcell hz hi0 hi

theorem ULHC.touch_beyond (hpvs : tf = s → 1 ≤ i → i0 ≤ i - 1) (hpv2 : 2 ≤ i → i0 ≤ i - 1) (hq : cellJ z tf i = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 = m) ∨ (tf = s.opp ∧ i % 2 = 0 ∧ i + 1 < m) ∨
      ((tf = latA s ∨ tf = latB s) ∧ i = 0) := by sorry
