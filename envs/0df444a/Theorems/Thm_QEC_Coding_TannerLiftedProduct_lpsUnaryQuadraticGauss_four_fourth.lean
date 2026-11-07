-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_four_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:17.280178+00:00
-- url     : https://prove2.me/theorems/8982f30e-b0b7-4c81-9b6b-375dcfef8ae6
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss four fourth
-- statement:
--   The actual modulus-four sum has fourth power minus four times the modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L203-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L203-L207

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four_fourth (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 4^4= -4*(4:ℂ)^2 := by sorry
