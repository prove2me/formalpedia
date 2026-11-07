-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDelta_j_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDelta_j_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:36:08.305413+00:00
-- url     : https://prove2.me/theorems/99cb5f19-69ef-4c52-8137-c3f95eb3b82a
-- title:
--   Tanner Lifted Product: lps Original Delta j power
-- statement:
--   Actual nowhere-zero Delta cancels in Delta^m*j^m=(E4^3)^m; used to reconstruct the induction polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L57-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L57-L61

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDelta_j_power (m : ℕ) (τ : ℍ) :
    ModularForm.discriminant τ^m*lpsOriginalJInvariant τ^m=(ModularForm.E₄ τ^3)^m := by sorry
