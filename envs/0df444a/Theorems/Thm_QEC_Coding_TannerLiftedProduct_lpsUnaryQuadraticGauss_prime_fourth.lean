-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_prime_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:37.045383+00:00
-- url     : https://prove2.me/theorems/a21a28aa-24c0-4e78-9e81-395eebbf78a1
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss prime fourth
-- statement:
--   The existing cyclic quadratic sum has fourth power p squared at an odd prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L62-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L62-L75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_fourth (p : ℕ) [Fact p.Prime]
    (hp2 : p≠2) (a : ℤ) (ha : (a:ZMod p)≠0) :
    lpsUnaryQuadraticGauss a p^4 = (p:ℂ)^2 := by sorry
