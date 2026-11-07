-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_comp_forgetLevel
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_comp_forgetLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:11:08.525311+00:00
-- url     : https://prove2.me/theorems/22f6970c-0dcc-43c0-9c64-77b2f69e769a
-- title:
--   Tanner Lifted Product: lps Original Filled Chart Meromorphic comp forget Level
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Filled Chart Meromorphic comp forget Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L24-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L24-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_comp_forgetLevel
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic M (dvd_trans hN hNM)
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) := by sorry
