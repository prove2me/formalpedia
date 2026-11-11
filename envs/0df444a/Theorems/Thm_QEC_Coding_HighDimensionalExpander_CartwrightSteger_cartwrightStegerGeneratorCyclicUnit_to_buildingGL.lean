-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:35:33.64259+00:00
-- url     : https://prove2.me/theorems/97c31f66-d406-4b2d-9353-a58ab35f9ee5
-- title:
--   Cartwright Steger: cartwright Steger Generator Cyclic Unit to building GL
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Generator Cyclic Unit to building GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L139-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L139-L148

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingGL
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicUnitToBuildingGL P r (cartwrightStegerGeneratorCyclicUnit P r u) =
      buildingCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) := by sorry
