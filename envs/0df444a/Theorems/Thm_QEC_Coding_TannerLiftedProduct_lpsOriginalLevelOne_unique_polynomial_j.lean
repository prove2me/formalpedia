-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_unique_polynomial_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_unique_polynomial_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:24.051232+00:00
-- url     : https://prove2.me/theorems/afb7ee1c-0de7-4b07-b87a-9f8f01b0bcfd
-- title:
--   Tanner Lifted Product: lps Original Level One unique polynomial j
-- statement:
--   The bounded-degree polynomial representation of any genuine level-one weight12m form is unique; used by the actual dilated-Delta norm polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L138-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L138-L148

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_unique_polynomial_j (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃! P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by sorry
