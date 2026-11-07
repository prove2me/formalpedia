-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_polynomial_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_polynomial_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:43:37.895322+00:00
-- url     : https://prove2.me/theorems/c8fb6427-b723-49e3-95e5-a4ab7501f068
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Norm polynomial nonzero
-- statement:
--   Actual nonzero norm excludes a zero recovered polynomial; this supplies the genuine denominator coefficient bridge for the forthcoming original modular equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L204-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L204-L218

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_polynomial_nonzero (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ P : Polynomial ℂ, P≠0 ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by sorry
