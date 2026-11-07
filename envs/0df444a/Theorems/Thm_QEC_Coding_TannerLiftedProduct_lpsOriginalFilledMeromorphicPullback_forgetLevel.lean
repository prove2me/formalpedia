-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicPullback_forgetLevel
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_forgetLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:08:51.750254+00:00
-- url     : https://prove2.me/theorems/5289238a-092f-439c-9874-3a9b89e87425
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic Pullback forget Level
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Filled Meromorphic Pullback forget Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L68-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L68-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_forgetLevel
    (N M : ℕ) (hNM : N ∣ M) (F : LPSOriginalFilledCurve N → ℂ) :
    lpsOriginalFilledMeromorphicPullback M
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) =
      lpsOriginalFilledMeromorphicPullback N F := by sorry
