-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withCollision_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.withCollision_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:28:50.716587+00:00
-- url     : https://prove2.me/theorems/9950f166-91db-4fff-8621-3e96041a9c41
-- title:
--   Light Weighted Global Seed Score: with Collision length
-- statement:
--   The Light Weighted Global Seed Score construction uses the with Collision length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L89-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L89-L91

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

theorem ThreeSum.LightWeightedGlobalSeedScore.withCollision_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withCollision p R S raws words maps).length=24 := by sorry
