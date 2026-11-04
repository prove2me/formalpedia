-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_program_length
-- name    : ThreeSum.LightWeightedGlobalGlobalPrelude.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:42:41.894555+00:00
-- url     : https://prove2.me/theorems/42c3aef9-14a7-46f5-9dce-bd71f1389423
-- title:
--   Light Weighted Global Global Prelude: program length
-- statement:
--   The Light Weighted Global Global Prelude construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryGlobalPrelude.lean#L63-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryGlobalPrelude.lean#L63-L63

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalGlobalPrelude
open Light

theorem ThreeSum.LightWeightedGlobalGlobalPrelude.program_length (M b p K κ : ℕ) : (program M b p K κ).length=50 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalGlobalPrelude.program_length
