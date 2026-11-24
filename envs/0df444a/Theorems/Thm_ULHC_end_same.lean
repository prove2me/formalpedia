-- Prove2me | Theorems.Thm_ULHC_end_same
-- name    : ULHC.end_same
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:58.604184+00:00
-- url     : https://prove2.me/theorems/242ba991-690e-46b5-a452-42e729900785
-- title:
--   ULHC: end same
-- statement:
--   The ULHC construction uses the end same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L301-L318
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L301-L318

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hT hk hcell hpat

theorem ULHC.end_same : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) := by sorry
