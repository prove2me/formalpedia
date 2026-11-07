-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_polynomial_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_polynomial_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:34:57.243446+00:00
-- url     : https://prove2.me/theorems/b6429009-1c47-4817-8694-fdfd3ca640ea
-- title:
--   Tanner Lifted Product: lps Original Level One polynomial j
-- statement:
--   Every genuine level-one weight12m modular form has a degree-at-most-m polynomial representation in the SAME original j; used by uniqueness and norm coefficient recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L64-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L64-L100

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_polynomial_j (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃ P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by sorry
