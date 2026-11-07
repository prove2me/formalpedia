-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_disjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:41.318605+00:00
-- url     : https://prove2.me/theorems/ebbf5fb6-0067-473f-a876-7ec44669e697
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood disjoint
-- statement:
--   Different genuine cusps have disjoint original high neighborhoods.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L188-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L188-L194

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_disjoint (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (Set.range (lpsOriginalCuspProjection N ρ))
      (Set.range (lpsOriginalCuspProjection N ρ')) := by sorry
