-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmetic_completion_compatibility
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:39:12.31459+00:00
-- url     : https://prove2.me/theorems/d749b48f-80d4-4403-bf26-2150b5afac25
-- title:
--   Cartwright Steger: integral Arithmetic completion compatibility
-- statement:
--   The global and integral realizations of `R_T` agree in `F_q((y))`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L59-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L59-L71

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility (P : BasePrime) :
    (SphericalHecke.integerEmbedding (BaseField P)).comp
        (integralArithmeticToBuildingIntegerRing P) =
      (functionFieldToBuildingLocalField P).comp
        (integralArithmeticToFunctionField P) := by sorry
