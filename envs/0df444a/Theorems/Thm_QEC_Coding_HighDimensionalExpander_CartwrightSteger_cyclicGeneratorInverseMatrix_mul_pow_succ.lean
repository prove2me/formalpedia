-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mul_pow_succ
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_mul_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:17.585281+00:00
-- url     : https://prove2.me/theorems/a562c349-5919-425a-a571-1f8c0ed37510
-- title:
--   Cartwright Steger: cyclic Generator Inverse Matrix mul pow succ
-- statement:
--   Cancellation of the inverse cyclic generator against a positive
--   power, in the exact predecessor form used by equation (9).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L174-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L174-L184

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_mul_pow_succ
    (P : BasePrime) (r : Rank) (n : ℕ) :
    cyclicGeneratorInverseMatrix P r *
        cyclicGeneratorMatrix P r ^ (n + 1) =
      cyclicGeneratorMatrix P r ^ n := by sorry
