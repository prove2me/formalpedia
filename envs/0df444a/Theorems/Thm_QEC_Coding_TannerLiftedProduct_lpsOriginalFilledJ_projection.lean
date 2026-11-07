-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:16.458336+00:00
-- url     : https://prove2.me/theorems/6ffde589-bc9d-42cd-80f7-cec257b56c26
-- title:
--   Tanner Lifted Product: lps Original Filled J projection
-- statement:
--   The exact same original upper-half-plane function is recovered by the filled orbit projection; used by the interior analytic proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L204-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L204-L205

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_projection (N : ℕ) (τ : ℍ) :
    lpsOriginalFilledJ N (Sum.inl ⟦τ⟧)=lpsOriginalJInvariant τ := by sorry
