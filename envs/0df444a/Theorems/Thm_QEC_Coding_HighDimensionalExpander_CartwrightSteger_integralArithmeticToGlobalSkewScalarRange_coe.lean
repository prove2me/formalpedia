-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:58:02.864049+00:00
-- url     : https://prove2.me/theorems/bcdee6bb-df8d-429d-922d-03a9bded4112
-- title:
--   Cartwright Steger: integral Arithmetic To Global Skew Scalar Range coe
-- statement:
--   The Cartwright Steger construction uses the integral Arithmetic To Global Skew Scalar Range coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L252-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean#L252-L268

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_coe
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P) :
    (integralArithmeticToGlobalSkewScalarRange P r a : FunctionField P) =
      integralArithmeticToFunctionField P a := by sorry
