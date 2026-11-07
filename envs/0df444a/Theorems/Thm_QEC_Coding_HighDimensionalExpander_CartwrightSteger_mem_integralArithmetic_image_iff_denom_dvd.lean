-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_integralArithmetic_image_iff_denom_dvd
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_integralArithmetic_image_iff_denom_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:27.338623+00:00
-- url     : https://prove2.me/theorems/36549f44-757f-4c6b-9dcd-bf66e37f667a
-- title:
--   Cartwright Steger: mem integral Arithmetic image iff denom dvd
-- statement:
--   The Cartwright Steger construction uses the mem integral Arithmetic image iff denom dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L18-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L18-L73

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_integralArithmetic_image_iff_denom_dvd
    (P : BasePrime) (x : FunctionField P) :
    (∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a = x) ↔
      ∃ n : ℕ, x.denom ∣
        (1 + Polynomial.X : PolynomialRing P) ^ n := by sorry
