-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withWanted_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.withWanted_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:23:41.876512+00:00
-- url     : https://prove2.me/theorems/a6add466-98a0-4f96-ad73-3b3ff6ce9443
-- title:
--   Light Weighted Global Seed Score: with Wanted length
-- statement:
--   The Light Weighted Global Seed Score construction uses the with Wanted length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L86-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L86-L88

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalSeedScore.withWanted_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withWanted p R S raws words maps).length=20 := by sorry
