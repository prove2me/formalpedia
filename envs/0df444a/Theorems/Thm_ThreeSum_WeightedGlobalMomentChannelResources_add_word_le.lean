-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_add_word_le
-- name    : ThreeSum.WeightedGlobalMomentChannelResources.add_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:34:26.080376+00:00
-- url     : https://prove2.me/theorems/ef24456e-a78e-4903-8cab-8b2edc90fe75
-- title:
--   Weighted Global Moment Channel Resources: add word le
-- statement:
--   The Weighted Global Moment Channel Resources construction uses the add word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L72-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L72-L84

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentChannelResources.add_word_le (B U K : ℕ) :
    2*((TernaryMomentSchedule.channels (K+1)).length*scoreBound B U K)≤(need B U K).word := by sorry
