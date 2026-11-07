-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_contMDiff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_contMDiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:40:18.663024+00:00
-- url     : https://prove2.me/theorems/cae34f70-fbb6-4e27-ab47-a68a1cdf7b7f
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level cont MDiff
-- statement:
--   At levels divisible by four the SAME original filled map is complex analytic everywhere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L332-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L332-L394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_contMDiff
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalFilledForgetLevel N M hNM) := by sorry
