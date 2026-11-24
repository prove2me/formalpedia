-- Prove2me | Theorems.Thm_ULHC_start_notTypeIII
-- name    : ULHC.start_notTypeIII
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:24.730767+00:00
-- url     : https://prove2.me/theorems/725c82ce-c896-465f-a86d-8dcbf1d66b2e
-- title:
--   ULHC: start not Type III
-- statement:
--   The ULHC construction uses the start not Type III property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L323-L339
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L323-L339

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.start_notTypeIII : NotTypeIII V (flipCol F c s (k + 2)) c := by sorry
