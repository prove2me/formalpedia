-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_square_scale
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:36.358571+00:00
-- url     : https://prove2.me/theorems/1d7903f0-ee5b-4746-99b4-f3268d0d1f36
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss odd square scale
-- statement:
--   Odd square scaling follows from actual mask projection and unit completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L283-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L283-L297

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_scale (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N=(d:ℂ)*lpsUnaryQuadraticGauss a N := by sorry
