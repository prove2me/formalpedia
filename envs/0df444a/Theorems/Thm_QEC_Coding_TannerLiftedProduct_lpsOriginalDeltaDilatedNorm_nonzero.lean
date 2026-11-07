-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:40.262726+00:00
-- url     : https://prove2.me/theorems/5e53059c-955d-44f6-840f-27b0a367d1aa
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Norm nonzero
-- statement:
--   Actual norm_ne_zero proves the genuine norm is a nonzero form; used to exclude the zero recovered polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L188-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L188-L190

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_nonzero (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalDeltaDilatedNorm N hN≠0 := by sorry
