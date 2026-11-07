-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_eight_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:20.216206+00:00
-- url     : https://prove2.me/theorems/3e05a887-4485-4535-ad54-0517920e120b
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss eight fourth
-- statement:
--   The actual modulus-eight sum has fourth power minus four times the modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L235-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L235-L238

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight_fourth (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8^4= -4*(8:ℂ)^2 := by sorry
