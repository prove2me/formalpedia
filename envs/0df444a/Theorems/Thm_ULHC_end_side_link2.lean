-- Prove2me | Theorems.Thm_ULHC_end_side_link2
-- name    : ULHC.end_side_link2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:01:11.279502+00:00
-- url     : https://prove2.me/theorems/dd64c8d9-3055-45fc-bd6d-1065fc67cb40
-- title:
--   ULHC: end side link2
-- statement:
--   The ULHC construction uses the end side link2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L192-L263
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L192-L263

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

theorem ULHC.end_side_link2 (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latB s), s, 1⟩ := by sorry
