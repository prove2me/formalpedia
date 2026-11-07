-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_eight
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:17.543442+00:00
-- url     : https://prove2.me/theorems/2f6892dd-8edc-4a8e-a112-5ee403480fad
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss eight
-- statement:
--   The eight actual terms give the modulus-eight quadratic sum at an odd coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L210-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L210-L232

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8=4*ZMod.stdAddChar (a:ZMod 8) := by sorry
