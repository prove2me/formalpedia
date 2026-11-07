-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4DilatedForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4DilatedForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:53:37.839202+00:00
-- url     : https://prove2.me/theorems/bd8fcf42-c683-46c6-acf6-38875962b51a
-- title:
--   Tanner Lifted Product: lps Original E4 Dilated Form apply
-- statement:
--   Literal pinned weight4 slash evaluation of the genuine translated E4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L44-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4DilatedForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalE4DilatedForm N hN τ=
      ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0) τ := by sorry
