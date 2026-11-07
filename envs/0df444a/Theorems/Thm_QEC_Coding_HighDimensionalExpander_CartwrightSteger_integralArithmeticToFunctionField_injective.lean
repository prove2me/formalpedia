-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:39:32.74341+00:00
-- url     : https://prove2.me/theorems/82ec5c60-1985-4a67-9565-83fdae8956c1
-- title:
--   Cartwright Steger: integral Arithmetic To Function Field injective
-- statement:
--   The global realization of `R_T` is faithful.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L83-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean#L83-L97

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_injective (P : BasePrime) :
    Function.Injective (integralArithmeticToFunctionField P) := by sorry
