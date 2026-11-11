-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:34:31.1202+00:00
-- url     : https://prove2.me/theorems/90ac87e4-f3c9-4eda-98ad-eba6ee5088db
-- title:
--   Cartwright Steger: cartwright Steger Generator Cyclic Unit coe
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Generator Cyclic Unit coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L124-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L124-L131

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_coe
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (cartwrightStegerGeneratorCyclicUnit P r u : CyclicAlgebra P r) =
      cartwrightStegerGeneratorCyclicElement P r u := by sorry
