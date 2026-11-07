-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:33.195176+00:00
-- url     : https://prove2.me/theorems/22251a21-8c6d-4711-ad64-7ed3e0f0da61
-- title:
--   Cartwright Steger: integral Arithmetic To Building Integer Ring injective
-- statement:
--   The integral realization of `R_T` in `F_q[[y]]` is faithful.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L100-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L100-L106

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_injective (P : BasePrime) :
    Function.Injective (integralArithmeticToBuildingIntegerRing P) := by sorry
