-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_range_subset
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:13.823059+00:00
-- url     : https://prove2.me/theorems/bc9a87f7-909d-4078-8b42-9d3e00fb0e58
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood range subset
-- statement:
--   The true cusp-representative change transports the whole original neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L127-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L127-L132

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_subset (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ')⊆Set.range (lpsOriginalCuspProjection N ρ) := by sorry
