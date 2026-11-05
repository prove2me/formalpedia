-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupBankStep_program_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupBankStep.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:17:05.096503+00:00
-- url     : https://prove2.me/theorems/dbb19e02-5c55-45c2-8364-03a4d79c3386
-- title:
--   program_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GroupBankStep.lean#L93-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GroupBankStep.lean#L93-L93

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankStep
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.program_length


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupBankStep.program_length : program.length=19 := by sorry
