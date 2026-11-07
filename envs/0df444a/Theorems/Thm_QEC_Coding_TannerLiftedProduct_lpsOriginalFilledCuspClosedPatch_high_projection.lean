-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_high_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_high_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:57.25623+00:00
-- url     : https://prove2.me/theorems/5259394c-e7c7-42c6-a165-b6a8142ed14c
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Closed Patch high projection
-- statement:
--   Every original height-two tail point lies in the selected true closed cusp patch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L199-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L199-L222

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_high_projection (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (σ : {τ : ℍ // 1<τ.im}) (hs : 2≤σ.val.im) :
    Sum.inl (lpsOriginalCuspProjection N ρ σ)∈
      lpsOriginalFilledCuspClosedPatch N (lpsOriginalCuspOrbit N ρ) := by sorry
