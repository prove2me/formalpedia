-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormInput_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:53:17.008643+00:00
-- url     : https://prove2.me/theorems/42da91de-61ca-4a20-8f60-6526b4840bb5
-- title:
--   Tanner Lifted Product: lps Original Modular Norm Input apply
-- statement:
--   Pointwise original norm input equals b_N*(jN-c).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L94-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L94-L100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_apply (N : ℕ) (hN : 0<N) (c : ℂ) (τ : ℍ) :
    lpsOriginalModularNormInput N hN c τ=
      lpsOriginalDeltaDilatedForm N hN τ*(lpsOriginalJDilated N hN τ-c) := by sorry
