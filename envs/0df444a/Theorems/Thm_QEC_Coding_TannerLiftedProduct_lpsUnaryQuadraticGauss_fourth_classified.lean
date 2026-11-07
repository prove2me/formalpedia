-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_fourth_classified
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth_classified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:51.331783+00:00
-- url     : https://prove2.me/theorems/c9860049-34d8-4a8e-ac1c-d763dabd3eac
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss fourth classified
-- statement:
--   Prime-power induction and actual CRT prove the complete fourth-power classification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L474-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L474-L494

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth_classified (N : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4=(lpsGaussFourthFactor N:ℂ)*(N:ℂ)^2 := by sorry
