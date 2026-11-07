-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_eval
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:52:37.675379+00:00
-- url     : https://prove2.me/theorems/6331231f-1da6-46bf-9486-93ff80632d35
-- title:
--   Tanner Lifted Product: lps Original Modular Coset Polynomial eval
-- statement:
--   Evaluation of the literal coset product at every c equals the actual input norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L183-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L183-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_eval (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) (c : ℂ) :
    (lpsOriginalModularCosetPolynomial N hN τ).eval c=
      lpsOriginalModularNorm N hN c τ := by sorry
