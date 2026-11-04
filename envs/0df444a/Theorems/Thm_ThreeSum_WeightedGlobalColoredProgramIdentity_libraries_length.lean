-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredProgramIdentity_libraries_length
-- name    : ThreeSum.WeightedGlobalColoredProgramIdentity.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:16:13.048019+00:00
-- url     : https://prove2.me/theorems/9cccd4e1-a88d-437b-99d3-6fc2dfbc0369
-- title:
--   Weighted Global Colored Program Identity: libraries length
-- statement:
--   The Weighted Global Colored Program Identity construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L37-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L37-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColoredSolver.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPreparedPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredProgramIdentity.libraries_length (P : Profile κ) : (libraries P).length=252 := by sorry
