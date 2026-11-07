-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_two_pow_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_two_pow_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:50.277195+00:00
-- url     : https://prove2.me/theorems/0e03d908-148f-4e44-b1aa-16ff0aa60b7e
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss two pow fourth
-- statement:
--   The actual four/eight bases and square reduction prove every higher two-power value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L399-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L399-L424

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_two_pow_fourth (e : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^(e+2)))) :
    lpsUnaryQuadraticGauss a (2^(e+2))^4= -4*((2^(e+2):ℕ):ℂ)^2 := by sorry
