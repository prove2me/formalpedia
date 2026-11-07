-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_range_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:55.892432+00:00
-- url     : https://prove2.me/theorems/115f1acd-b5ba-4c74-b5ab-fcee62e0982e
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood range eq
-- statement:
--   Representatives of the same actual cusp give the same original neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L135-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L135-L139

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_eq (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ)=Set.range (lpsOriginalCuspProjection N ρ') := by sorry
