-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_sameCuspCoordinate
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_sameCuspCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:45.246745+00:00
-- url     : https://prove2.me/theorems/14c2173d-f83b-4fbf-832c-7aa953ff21f9
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level same Cusp Coordinate
-- statement:
--   The actual coordinate on the entire cusp source is the genuine positive width-ratio power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L116-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L116-L135

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_sameCuspCoordinate (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledCuspPartialEquiv N ρ (lpsOriginalFilledForgetLevel N M hNM x) =
      (lpsOriginalFilledCuspPartialEquiv M ρ x) ^ lpsOriginalCuspLevelDegree N M ρ := by sorry
