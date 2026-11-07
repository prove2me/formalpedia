-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cuspSource
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspSource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:32.06664+00:00
-- url     : https://prove2.me/theorems/c66d29cf-1f2c-40a6-9c69-62cffc6e9ca4
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level cusp Source
-- statement:
--   The SAME original level map preserves the whole represented cusp source, including the cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L99-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L99-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspSource (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledForgetLevel N M hNM x ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source := by sorry
