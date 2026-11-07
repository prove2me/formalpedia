-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormCoefficient_spec
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormCoefficient_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:10.284282+00:00
-- url     : https://prove2.me/theorems/dd465b70-e84d-4c3b-933c-28a6fab01905
-- title:
--   Tanner Lifted Product: lps Original Modular Norm Coefficient spec
-- statement:
--   Actual coefficient polynomial has bounded degree and recovers the genuine norm at every tau.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L236-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L236-L243

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormCoefficient_spec (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormCoefficient N hN c).natDegree≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          (lpsOriginalModularNormCoefficient N hN c).eval (lpsOriginalJInvariant τ) := by sorry
