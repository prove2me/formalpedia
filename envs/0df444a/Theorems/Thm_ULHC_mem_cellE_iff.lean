-- Prove2me | Theorems.Thm_ULHC_mem_cellE_iff
-- name    : ULHC.mem_cellE_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:41:27.075083+00:00
-- url     : https://prove2.me/theorems/3304420d-cbab-426e-9a3d-2dc948dfb829
-- title:
--   ULHC: mem cell E iff
-- statement:
--   The ULHC construction uses the mem cell E iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L801-L802
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L801-L802

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.mem_cellE_iff (e : Edge) (c : Pt) : e ∈ cellE c ↔ (e.hi = c ∨ e.lo = c) := by sorry
