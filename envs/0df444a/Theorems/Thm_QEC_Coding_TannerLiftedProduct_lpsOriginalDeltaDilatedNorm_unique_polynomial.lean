-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_unique_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_unique_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:36:03.786206+00:00
-- url     : https://prove2.me/theorems/ce6ace89-be79-4139-9d94-41ad4ebd5e98
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Norm unique polynomial
-- statement:
--   The genuine original dilated-Delta norm has a UNIQUE polynomial in SAME j of degree at most the actual coset cardinal; used to obtain a nonzero polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L193-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L193-L201

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_unique_polynomial (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃! P : Polynomial ℂ,
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by sorry
