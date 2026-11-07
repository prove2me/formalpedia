-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:08:37.078629+00:00
-- url     : https://prove2.me/theorems/df110750-49dd-4c99-b066-4f4f968d76d5
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic Restriction Subfield level le
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Filled Meromorphic Restriction Subfield level le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L76-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    lpsOriginalFilledMeromorphicRestrictionSubfield N hN ≤
      lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) := by sorry
