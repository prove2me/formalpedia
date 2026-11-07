-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_prime_pow_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_prime_pow_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:38.571578+00:00
-- url     : https://prove2.me/theorems/32148780-8fd8-41d2-a962-6e8cf40f8d43
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss odd prime pow fourth
-- statement:
--   Odd square reduction proves the fourth-power value at every odd prime power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L373-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L373-L396

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_prime_pow_fourth (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=((p^e:ℕ):ℂ)^2 := by sorry
