-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_length
-- name    : ThreeSum.LightWeightedGlobalMomentReporter.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:22:09.48142+00:00
-- url     : https://prove2.me/theorems/f2162bc4-45b6-46c5-973a-53804f705a16
-- title:
--   Light Weighted Global Moment Reporter: program length
-- statement:
--   The Light Weighted Global Moment Reporter construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L37-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L37-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDriverResources
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_program_length
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedRows_program_length
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryCountFrontend.program_length
attribute [local simp] ThreeSum.LightTernaryGroupedBanks.program_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
attribute [local simp] ThreeSum.LightTernaryNearSetup.program_length
attribute [local simp] ThreeSum.LightTernaryPreparedWanted.program_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.program_length
attribute [local simp] ThreeSum.LightTernaryWantedQuery.program_length
attribute [local simp] ThreeSum.LightTernaryWantedRows.program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalCertifiedMomentDriver.program_length
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem ThreeSum.LightWeightedGlobalMomentReporter.program_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    (program S H).length=139*(channels (2*H+1)).length+7 := by sorry
