-- Prove2me | Theorems.Thm_ULHC_side_mem_cellE_nb
-- name    : ULHC.side_mem_cellE_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:43:03.556263+00:00
-- url     : https://prove2.me/theorems/5fba20dd-49b7-4e03-a735-82e95b86f285
-- title:
--   ULHC: side mem cell E nb
-- statement:
--   The ULHC construction uses the side mem cell E nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L877-L879
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L877-L879

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.side_mem_cellE_nb (c : Pt) (s : Side) : sideEdge c s ∈ cellE (nb c s) := by sorry
