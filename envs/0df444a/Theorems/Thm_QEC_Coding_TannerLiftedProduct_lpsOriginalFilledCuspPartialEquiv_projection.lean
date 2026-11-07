-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:54.908203+00:00
-- url     : https://prove2.me/theorems/600d00ca-29cb-4a4d-bbd7-b92285b1047c
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv projection
-- statement:
--   The filled coordinate still computes the SAME actual original minimal-width q parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L124-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L124-L132

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_projection (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inl (lpsOriginalCuspProjection N ρ τ))=
      Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ.val := by sorry
