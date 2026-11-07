-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:04.717046+00:00
-- url     : https://prove2.me/theorems/b42ef610-db10-4611-92f2-aeb25ceaa910
-- title:
--   Cartwright Steger: building Cyclic Generator PGL mem compact Cyclic Subgroup
-- statement:
--   The Cartwright Steger construction uses the building Cyclic Generator PGL mem compact Cyclic Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L612-L615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L612-L615

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorPGL P r ∈ BuildingCompactCyclicSubgroup P r := by sorry
