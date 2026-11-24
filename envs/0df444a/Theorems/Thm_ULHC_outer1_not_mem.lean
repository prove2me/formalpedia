-- Prove2me | Theorems.Thm_ULHC_outer1_not_mem
-- name    : ULHC.outer1_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:28:52.013871+00:00
-- url     : https://prove2.me/theorems/1b00db3b-a5b7-463f-bd62-39faf172e167
-- title:
--   ULHC: outer1 not mem
-- statement:
--   The ULHC construction uses the outer1 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L55-L57
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L55-L57

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer1_not_mem (j m : ℕ) : outer1 (cellJ c s j) s ∉ cellE (cellJ c s m) := by sorry
