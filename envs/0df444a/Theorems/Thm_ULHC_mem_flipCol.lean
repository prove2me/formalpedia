-- Prove2me | Theorems.Thm_ULHC_mem_flipCol
-- name    : ULHC.mem_flipCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:35.761952+00:00
-- url     : https://prove2.me/theorems/8bbaf862-e90b-4cfa-b504-edf8a416d471
-- title:
--   ULHC: mem flip Col
-- statement:
--   The ULHC construction uses the mem flip Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L702-L717
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L702-L717

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.mem_flipCol (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ n e, e ∈ flipCol F c s n ↔ (e ∈ F ↔ nOn c s n e % 2 = 0) := by sorry
