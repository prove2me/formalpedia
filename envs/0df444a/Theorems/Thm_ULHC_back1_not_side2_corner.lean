-- Prove2me | Theorems.Thm_ULHC_back1_not_side2_corner
-- name    : ULHC.back1_not_side2_corner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:53:54.361421+00:00
-- url     : https://prove2.me/theorems/2efe81d1-9aa2-4a06-b41f-fd42876be212
-- title:
--   ULHC: back1 not side2 corner
-- statement:
--   The ULHC construction uses the back1 not side2 corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L251-L255
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L251-L255

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

theorem ULHC.back1_not_side2_corner (c : Pt) (s : Side) :
    back1 c s ∉ ({back1 (nb c (latB s)) s, back2 (nb c (latB s)) s, front1 (nb c (latB s)) s,
      front2 (nb c (latB s)) s} : Finset Pt) := by sorry
