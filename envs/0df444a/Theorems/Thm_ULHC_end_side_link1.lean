-- Prove2me | Theorems.Thm_ULHC_end_side_link1
-- name    : ULHC.end_side_link1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:06.709319+00:00
-- url     : https://prove2.me/theorems/c244d3ce-3af9-41f8-9b80-3d22de867cf2
-- title:
--   ULHC: end side link1
-- statement:
--   The ULHC construction uses the end side link1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L122-L190
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L122-L190

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.end_side_link1 (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by sorry
