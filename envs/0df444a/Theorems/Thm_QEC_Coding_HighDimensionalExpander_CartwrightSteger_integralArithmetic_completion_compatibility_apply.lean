-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmetic_completion_compatibility_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:39:34.02368+00:00
-- url     : https://prove2.me/theorems/5a1b0881-25ae-44cd-9adb-024efa37150a
-- title:
--   Cartwright Steger: integral Arithmetic completion compatibility apply
-- statement:
--   Pointwise form of `integralArithmetic_completion_compatibility`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L74-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L74-L80

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility_apply
    (P : BasePrime) (x : IntegralArithmeticRing P) :
    SphericalHecke.integerEmbedding (BaseField P)
        (integralArithmeticToBuildingIntegerRing P x) =
      functionFieldToBuildingLocalField P
        (integralArithmeticToFunctionField P x) := by sorry
