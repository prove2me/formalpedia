-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:53:42.381834+00:00
-- url     : https://prove2.me/theorems/e2940781-7a08-42a3-aeff-7fea8d934d13
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss fourth
-- statement:
--   A modulus divisible by four gives the exact unit fourth power minus four times N squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L497-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L497-L504

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth (N : ℕ) (hN : 4 ∣ N) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4= -4*(N:ℂ)^2 := by sorry
