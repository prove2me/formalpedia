-- Prove2me | Theorems.Thm_ULHC_side_mem_self
-- name    : ULHC.side_mem_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:09.53006+00:00
-- url     : https://prove2.me/theorems/ead694c3-2adf-4ac3-811b-48e30c34c596
-- title:
--   ULHC: side mem self
-- statement:
--   The ULHC construction uses the side mem self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L24-L25
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L24-L25

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.side_mem_self (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE c := by sorry
