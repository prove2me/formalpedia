-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_program_length
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:54:18.497428+00:00
-- url     : https://prove2.me/theorems/32d1a3a0-63d5-40e2-8047-a553e79a7cc4
-- title:
--   Light Weighted Global Prefix Loop: program length
-- statement:
--   The Light Weighted Global Prefix Loop construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L124-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L124-L126

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_program_length
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
import Theorems.Thm_ThreeSum_LightStoredSpan_program_length
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedController_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
attribute [local simp] ThreeSum.LightOriginalCollisionScore.program_length
attribute [local simp] ThreeSum.LightStoredSpan.program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedController.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.program_length
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.program_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (program p R S K raws words maps xl yl zl xr yr zr).length=197 := by sorry
