-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantMatrix_unit_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_unit_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:37:25.653363+00:00
-- url     : https://prove2.me/theorems/72abf7c3-540d-47e1-b405-e51a8981c272
-- title:
--   Cartwright Steger: building Constant Matrix unit inv
-- statement:
--   The Cartwright Steger construction uses the building Constant Matrix unit inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L581-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L581-L604

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_unit_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantMatrix P r ((u : ConstantExtension P r)⁻¹) =
      (buildingConstantMatrix P r (u : ConstantExtension P r))⁻¹ := by sorry
