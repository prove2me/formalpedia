-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_nonconstant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_nonconstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:27:13.408322+00:00
-- url     : https://prove2.me/theorems/761d7037-eda8-4d06-ab5c-b8604981ef49
-- title:
--   Tanner Lifted Product: lps Original Filled J nonconstant
-- statement:
--   Nonconstancy of the filled meromorphic function follows through the actual orbit projection; immediate input to original function-field/model comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L380-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L380-L384

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_nonconstant (N : ℕ) :
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJ N x=c := by sorry
