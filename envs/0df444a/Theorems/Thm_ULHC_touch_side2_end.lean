-- Prove2me | Theorems.Thm_ULHC_touch_side2_end
-- name    : ULHC.touch_side2_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:17:48.275085+00:00
-- url     : https://prove2.me/theorems/a17d3786-481b-4162-bcf0-204ac2cecabe
-- title:
--   ULHC: touch side2 end
-- statement:
--   The ULHC construction uses the touch side2 end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L531-L566
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L531-L566

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
include hF hk hcell hpat hz hi0 hi

theorem ULHC.touch_side2_end (hq : cellJ z tf i = nb (cellJ c s (k + 1)) (latB s)) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 < m) ∨
      (tf = latA s ∧ outer2 (cellJ c s (k + 1)) s ∈ F ∧
        lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) := by sorry
