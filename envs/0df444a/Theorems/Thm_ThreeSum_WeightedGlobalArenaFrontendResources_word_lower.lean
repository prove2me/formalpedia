-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontendResources_word_lower
-- name    : ThreeSum.WeightedGlobalArenaFrontendResources.word_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:45:04.537226+00:00
-- url     : https://prove2.me/theorems/b2efc992-a6b2-4d2f-a419-9d35671fcd74
-- title:
--   Weighted Global Arena Frontend Resources: word lower
-- statement:
--   The Weighted Global Arena Frontend Resources construction uses the word lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L27-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L27-L37

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaFrontendResources.word_lower (N nb groups count R A : ℕ) :
    10000*(N+R+100)≤word N nb groups count R A := by sorry
