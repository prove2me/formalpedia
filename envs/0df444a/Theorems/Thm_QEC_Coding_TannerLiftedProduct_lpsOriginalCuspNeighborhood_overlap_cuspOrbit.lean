-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_overlap_cuspOrbit
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_overlap_cuspOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:17.959708+00:00
-- url     : https://prove2.me/theorems/0c28a15e-395d-4911-bde7-13aee51004e4
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood overlap cusp Orbit
-- statement:
--   An overlap of true high neighborhoods forces equality of actual cusp orbits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L160-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L160-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_overlap_cuspOrbit (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (τ σ : {τ : ℍ // 1<τ.im})
    (he : lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by sorry
