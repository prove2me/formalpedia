-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNumeratorForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNumeratorForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:53:14.884811+00:00
-- url     : https://prove2.me/theorems/f8a14af6-8d2c-4a02-9f9b-3b4dbf5a5749
-- title:
--   Tanner Lifted Product: lps Original JNumerator Form apply
-- statement:
--   Literal cubic slash formula for the determinant-corrected original numerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L54-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L54-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNumeratorForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJNumeratorForm N hN τ=(N:ℂ)^2*
      (((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0) τ)^3 := by sorry
