-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_unit_inv
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrix_unit_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:38:13.022314+00:00
-- url     : https://prove2.me/theorems/9f9c2d09-b31b-45a4-8577-9e8f64c75a99
-- title:
--   Cartwright Steger: constant Matrix unit inv
-- statement:
--   The Cartwright Steger construction uses the constant Matrix unit inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L606-L629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L606-L629

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrix_unit_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantMatrix P r ((u : ConstantExtension P r)⁻¹) =
      (constantMatrix P r (u : ConstantExtension P r))⁻¹ := by sorry
