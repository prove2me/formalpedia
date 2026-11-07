-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormInput_quotient_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_quotient_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:54:54.406104+00:00
-- url     : https://prove2.me/theorems/d812df49-399d-44a0-b0e4-22bfee9f9432
-- title:
--   Tanner Lifted Product: lps Original Modular Norm Input quotient apply
-- statement:
--   Actual quotientFunc linearity for the genuine numerator-minus-c-Delta input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L155-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L155-L169

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_quotient_apply (N : ℕ) (hN : 0<N) (c : ℂ)
    (q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    (τ : ℍ) :
    SlashInvariantForm.quotientFunc (lpsOriginalModularNormInput N hN c) q τ=
      SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ-
        c*SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ := by sorry
