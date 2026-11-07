-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteField_square_sum_fourth
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:40.226668+00:00
-- url     : https://prove2.me/theorems/0f905e2e-db9d-4901-9850-90a6ad0be5c2
-- title:
--   Tanner Lifted Product: lps Finite Field square sum fourth
-- statement:
--   The genuine finite-field quadratic sum has fourth power equal to the squared field cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L46-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L46-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_fourth (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2))^4 = (Fintype.card F:ℂ)^2 := by sorry
