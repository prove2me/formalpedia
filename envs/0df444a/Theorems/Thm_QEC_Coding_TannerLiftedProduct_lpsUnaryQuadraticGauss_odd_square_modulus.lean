-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_square_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:26.913217+00:00
-- url     : https://prove2.me/theorems/f0a5cac1-39b4-4934-975b-a8e78a6f2e69
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss odd square modulus
-- statement:
--   Odd square scaling and inflation remove a square factor from the actual modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L300-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L300-L314

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_modulus (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss a N=(d:ℂ)*lpsUnaryQuadraticGauss a k := by sorry
