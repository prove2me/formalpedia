-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQuotient_nonconstant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJQuotient_nonconstant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:24:45.871917+00:00
-- url     : https://prove2.me/theorems/094218f6-994a-4b18-aa3d-3acbcbe6f33d
-- title:
--   Tanner Lifted Product: lps Original JQuotient nonconstant
-- statement:
--   The descended original quotient function is not constant; used by the root fixture and immediate original function-field construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L155-L159

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJQuotient_nonconstant (N : ℕ) :
    ¬∃ c : ℂ, ∀ x, lpsOriginalJQuotient N x=c := by sorry
