-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:34:55.976237+00:00
-- url     : https://prove2.me/theorems/ab54fb1c-0fa2-49fe-b410-cc64bc79794c
-- title:
--   Cartwright Steger: cartwright Steger Generator Cyclic Unit to building PGL
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Generator Cyclic Unit to building PGL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L160-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L160-L169

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicUnitToBuildingPGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u) =
      buildingCartwrightStegerGenerator P r u := by sorry
