-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_change_point
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_change_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:51.444353+00:00
-- url     : https://prove2.me/theorems/85646b46-e1ff-46fd-8f4b-7ca0f7b9a050
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood change point
-- statement:
--   Changing representatives of the same true cusp preserves the original projected point and height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L107-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L107-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_change_point (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ')
    (σ : {τ : ℍ // 1<τ.im}) :
    ∃ τ : {τ : ℍ // 1<τ.im}, τ.val.im=σ.val.im ∧
      lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ := by sorry
