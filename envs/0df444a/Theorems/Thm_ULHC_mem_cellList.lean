-- Prove2me | Theorems.Thm_ULHC_mem_cellList
-- name    : ULHC.mem_cellList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:18.565849+00:00
-- url     : https://prove2.me/theorems/9934a93b-2156-46cb-8037-9b944b453811
-- title:
--   ULHC: mem cell List
-- statement:
--   The ULHC construction uses the mem cell List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L27-L32
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L27-L32

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.mem_cellList {V : Finset Pt} {d : Pt} : d ∈ cellList V ↔ d ∈ V ∧ IsCell V d := by sorry
