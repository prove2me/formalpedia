-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:09.83621+00:00
-- url     : https://prove2.me/theorems/9d269df3-3e1a-41c6-b4d4-7e46978f0963
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level continuous
-- statement:
--   The SAME whole original filled map is continuous by the actual cusp-gluing universal property.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L305-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L305-L329

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_continuous
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    Continuous (lpsOriginalFilledForgetLevel N M hNM) := by sorry
