-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_program_split
-- name    : ThreeSum.LightWeightedGlobalTensorFactory.program_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:31:21.438089+00:00
-- url     : https://prove2.me/theorems/25adcbd7-1969-4bbd-a3e8-2664616a9477
-- title:
--   Light Weighted Global Tensor Factory: program split
-- statement:
--   The Light Weighted Global Tensor Factory construction uses the program split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactory.lean#L41-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactory.lean#L41-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriverProof
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatchFinal
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType

theorem ThreeSum.LightWeightedGlobalTensorFactory.program_split {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (K : ℕ) :
    program S K=S.program++extras K := by sorry
