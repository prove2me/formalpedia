-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNorm_polynomial_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_polynomial_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:14:32.301666+00:00
-- url     : https://prove2.me/theorems/a044aef3-94fd-45cf-a3ee-454e21ebe637
-- title:
--   Tanner Lifted Product: lps Original Modular Norm polynomial nonzero
-- statement:
--   Actual nonzero original input norm has a nonzero coefficient polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L137-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L137-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_polynomial_nonzero (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ∃ P : Polynomial ℂ, P≠0 ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by sorry
