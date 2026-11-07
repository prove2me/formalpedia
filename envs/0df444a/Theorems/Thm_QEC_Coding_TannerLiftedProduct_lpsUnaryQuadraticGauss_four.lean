-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_four
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:17.677201+00:00
-- url     : https://prove2.me/theorems/076e7911-66a8-418f-8efb-526be37932c6
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss four
-- statement:
--   The four actual terms give the modulus-four quadratic sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L188-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L188-L200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four (a : ℤ) :
    lpsUnaryQuadraticGauss a 4=2+2*ZMod.stdAddChar (a:ZMod 4) := by sorry
