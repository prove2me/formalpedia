-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_isProperMap
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_isProperMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:40:13.890782+00:00
-- url     : https://prove2.me/theorems/0283e077-7d6d-44a5-8d2f-0f2d5aec11d6
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level is Proper Map
-- statement:
--   The actual continuous level map is proper by genuine original compactness and Hausdorffness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L398-L407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L398-L407

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_isProperMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    IsProperMap (lpsOriginalFilledForgetLevel N M hNM) := by sorry
