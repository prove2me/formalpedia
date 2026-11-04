-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_wanted_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.wanted_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:23:38.058761+00:00
-- url     : https://prove2.me/theorems/07b2f30f-4179-411d-94fe-3459de9c8fb6
-- title:
--   Light Weighted Global Seed Score: wanted length
-- statement:
--   The Light Weighted Global Seed Score construction uses the wanted length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L84-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L84-L85

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

theorem ThreeSum.LightWeightedGlobalSeedScore.wanted_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (LightTernaryWantedBatch.program p R S raws words maps).length=5 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalSeedScore.wanted_length
