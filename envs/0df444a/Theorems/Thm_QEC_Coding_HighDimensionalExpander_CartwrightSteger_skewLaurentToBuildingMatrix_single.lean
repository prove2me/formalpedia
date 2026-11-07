-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:56.942089+00:00
-- url     : https://prove2.me/theorems/6449521e-506c-4cb5-8808-e68cdfacb2c5
-- title:
--   Cartwright Steger: skew Laurent To Building Matrix single
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Building Matrix single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L238-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean#L238-L246

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ)
    (c : ConstantExtension P r) :
    skewLaurentToBuildingMatrix P r
        (SkewMonoidAlgebra.single n c) =
      buildingConstantMatrix P r c * buildingCyclicZMatrixHom P r n := by sorry
