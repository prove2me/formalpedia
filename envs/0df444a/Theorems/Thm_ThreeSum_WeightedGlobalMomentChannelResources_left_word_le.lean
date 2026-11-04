-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_left_word_le
-- name    : ThreeSum.WeightedGlobalMomentChannelResources.left_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:34:54.472337+00:00
-- url     : https://prove2.me/theorems/a10f77a5-875e-497b-b299-9d0aff20dbde
-- title:
--   Weighted Global Moment Channel Resources: left word le
-- statement:
--   The Weighted Global Moment Channel Resources construction uses the left word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L51-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L51-L60

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentChannelResources.left_word_le (B U K : ℕ) : leftWord U K≤(need B U K).word := by sorry
