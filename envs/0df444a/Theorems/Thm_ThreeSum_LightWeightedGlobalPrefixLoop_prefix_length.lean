-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_prefix_length
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.prefix_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:05.978229+00:00
-- url     : https://prove2.me/theorems/1787f25a-269f-4004-9d75-85feb4bf0768
-- title:
--   Light Weighted Global Prefix Loop: prefix length
-- statement:
--   The Light Weighted Global Prefix Loop construction uses the prefix length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L118-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L118-L122

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.prefix_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (priorProcs p R S K raws words maps xl yl zl xr yr zr).length=190 := by sorry
