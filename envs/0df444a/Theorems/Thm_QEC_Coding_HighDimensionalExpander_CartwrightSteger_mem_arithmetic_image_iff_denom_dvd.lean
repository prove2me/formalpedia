-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmetic_image_iff_denom_dvd
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmetic_image_iff_denom_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:48.441258+00:00
-- url     : https://prove2.me/theorems/391b4f98-5ef2-40d7-b713-1479b3b1ec22
-- title:
--   Cartwright Steger: mem arithmetic image iff denom dvd
-- statement:
--   The Cartwright Steger construction uses the mem arithmetic image iff denom dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L75-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticIntersection.lean#L75-L119

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmetic_image_iff_denom_dvd
    (P : BasePrime) (x : FunctionField P) :
    (∃ a : ArithmeticRing P,
        arithmeticRingToFunctionField P a = x) ↔
      ∃ n : ℕ, x.denom ∣
        (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P) ^ n := by sorry
