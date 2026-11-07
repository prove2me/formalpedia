-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhoodChart_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhoodChart_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:42.283204+00:00
-- url     : https://prove2.me/theorems/50a8500c-074f-4a8a-b1ad-a9fe1bcacc4d
-- title:
--   Tanner Lifted Product: lps Original Cusp Neighborhood Chart projection
-- statement:
--   The actual original-neighborhood homeomorphism sends projections to the genuine q coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNeighborhoods.lean#L285-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNeighborhoods.lean#L285-L296

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Maps.Strict.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhoodChart_projection (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalCuspNeighborhoodChart N ρ ⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩=
      lpsOriginalCuspCoordinate N ρ τ := by sorry
