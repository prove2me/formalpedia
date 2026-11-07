-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstant_conj_frobeniusMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_conj_frobeniusMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:22.155907+00:00
-- url     : https://prove2.me/theorems/b83af6b6-39e4-4561-9ea2-eb64b5871134
-- title:
--   Cartwright Steger: building Constant conj frobenius Matrix
-- statement:
--   The Cartwright Steger construction uses the building Constant conj frobenius Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L37-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingConstantKernel.lean#L37-L49

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstant_conj_frobeniusMatrix
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantMatrix P r u * buildingFrobeniusMatrix P r *
        buildingConstantMatrix P r (u⁻¹ : (ConstantExtension P r)ˣ) =
      buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
        buildingFrobeniusMatrix P r := by sorry
