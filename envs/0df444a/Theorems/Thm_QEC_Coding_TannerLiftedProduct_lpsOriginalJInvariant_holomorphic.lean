-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:26.79745+00:00
-- url     : https://prove2.me/theorems/9a4430f6-a9e2-4fde-a2bd-c8febbddf44f
-- title:
--   Tanner Lifted Product: lps Original JInvariant holomorphic
-- statement:
--   Genuine upper-half-plane holomorphy using actual Delta nowhere zero; used by the interior coordinate analytic proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L52-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_holomorphic :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) lpsOriginalJInvariant := by sorry
