-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_pair_card_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.pair_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:02:26.710126+00:00
-- url     : https://prove2.me/theorems/67f0cfcf-b451-47a6-b822-7dd9fca5a678
-- title:
--   Weighted Global Native Moment Bounds: pair card le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the pair card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L28-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L28-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.pair_card_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :
    Fintype.card (Pair S i)≤pairBound S := by sorry
