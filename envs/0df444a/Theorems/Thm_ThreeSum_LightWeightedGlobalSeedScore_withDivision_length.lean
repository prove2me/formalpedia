-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withDivision_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.withDivision_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:20:18.659797+00:00
-- url     : https://prove2.me/theorems/86f91722-2b2a-4541-851c-986276282e22
-- title:
--   Light Weighted Global Seed Score: with Division length
-- statement:
--   The Light Weighted Global Seed Score construction uses the with Division length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L92-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L92-L94

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

theorem ThreeSum.LightWeightedGlobalSeedScore.withDivision_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withDivision p R S raws words maps).length=25 := by sorry
