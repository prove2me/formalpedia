-- Prove2me | Theorems.Thm_ULHC_side_mem_cellE_iff
-- name    : ULHC.side_mem_cellE_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:48.01037+00:00
-- url     : https://prove2.me/theorems/7238f039-e260-4949-b7de-93afda0c9448
-- title:
--   ULHC: side mem cell E iff
-- statement:
--   The ULHC construction uses the side mem cell E iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L52-L57
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L52-L57

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.side_mem_cellE_iff (c : Pt) (tf : Side) (x : Pt) :
    sideEdge c tf ∈ cellE x ↔ x = c ∨ x = nb c tf := by sorry
