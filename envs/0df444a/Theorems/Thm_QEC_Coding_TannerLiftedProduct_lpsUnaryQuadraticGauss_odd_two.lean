-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:40.22096+00:00
-- url     : https://prove2.me/theorems/28c98128-03aa-4b07-ae7e-daabeda3d85b
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss odd two
-- statement:
--   The two actual terms cancel for an odd coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L350-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L350-L370

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_two (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 2=0 := by sorry
