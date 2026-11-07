-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mul_constantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_mul_constantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:24.867216+00:00
-- url     : https://prove2.me/theorems/5d902030-66f1-485c-a62f-e0e0a2020e54
-- title:
--   Cartwright Steger: cyclic Generator Inverse Matrix mul constant Matrix
-- statement:
--   The inverse cyclic generator obeys the inverse-Frobenius skew
--   relation on arbitrary constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L117-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L117-L137

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_mul_constantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    cyclicGeneratorInverseMatrix P r * constantMatrix P r c =
      constantMatrix P r ((constantFrobenius P r).symm c) *
        cyclicGeneratorInverseMatrix P r := by sorry
