-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:29:01.546225+00:00
-- url     : https://prove2.me/theorems/a67b5a97-d7bb-4442-94d9-7aa6ee5bdcc1
-- title:
--   Light Weighted Global Seed Score: libraries length
-- statement:
--   The Light Weighted Global Seed Score construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L95-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L95-L98

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalSeedScore.libraries_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (libraries p R S K raws words maps xl yl zl xr yr zr).length=176 := by sorry
