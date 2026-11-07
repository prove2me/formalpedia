-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_mul_constantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_pow_mul_constantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:54.665219+00:00
-- url     : https://prove2.me/theorems/c8db6f8e-5dc8-4a0f-965c-b5fb5b47efcb
-- title:
--   Cartwright Steger: cyclic Generator Matrix pow mul constant Matrix
-- statement:
--   Matrix skew relation for every natural power and every constant,
--   including zero.  This is the workhorse for expanding equation (9).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L86-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L86-L113

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_pow_mul_constantMatrix
    (P : BasePrime) (r : Rank) (j : ℕ) (c : ConstantExtension P r) :
    cyclicGeneratorMatrix P r ^ j * constantMatrix P r c =
      constantMatrix P r ((constantFrobenius P r ^ j) c) *
        cyclicGeneratorMatrix P r ^ j := by sorry
