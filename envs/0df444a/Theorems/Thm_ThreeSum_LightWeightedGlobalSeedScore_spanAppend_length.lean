-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_spanAppend_length
-- name    : ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:23:34.667182+00:00
-- url     : https://prove2.me/theorems/5b0fe180-62ea-484d-bfd2-097fc6b82a4a
-- title:
--   Light Weighted Global Seed Score: span Append length
-- statement:
--   The Light Weighted Global Seed Score construction uses the span Append length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L83-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L83-L83

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

theorem ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length : spanAppend.length=15 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length
