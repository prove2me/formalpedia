-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:20:14.393008+00:00
-- url     : https://prove2.me/theorems/e8cd7f7a-203e-4a89-9b4a-8a7754776ae0
-- title:
--   Cartwright Steger: cyclic Generator Inverse Matrix eq inv smul pow pred
-- statement:
--   The inverse cyclic generator is the normalized `(d - 1)`-st power.
--   This converts the only negative cyclic exponent in equation (9) into the
--   finite basis range `0, ..., d - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L142-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L142-L161

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r =
      (onePlusY P r)⁻¹ •
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) := by sorry
