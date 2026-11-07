-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_coprime_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_coprime_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:52.946192+00:00
-- url     : https://prove2.me/theorems/e0b1fa60-d530-452e-b886-01d75754faac
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss coprime mul
-- statement:
--   Constructed CRT reindexing factors the genuine sum at coprime moduli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L120-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L120-L144

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ℤ) :
    lpsUnaryQuadraticGauss a (m*n) =
      lpsUnaryQuadraticGauss (a*(n:ℤ)) m * lpsUnaryQuadraticGauss (a*(m:ℤ)) n := by sorry
