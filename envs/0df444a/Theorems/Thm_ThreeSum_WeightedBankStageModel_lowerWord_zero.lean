-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_zero
-- name    : ThreeSum.WeightedBankStageModel.lowerWord_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:47.698568+00:00
-- url     : https://prove2.me/theorems/10a506ab-84ad-4e10-b55f-24e80b555772
-- title:
--   Weighted Bank Stage Model: lower Word zero
-- statement:
--   The Weighted Bank Stage Model construction uses the lower Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L33-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L33-L36

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedBankStageModel.lowerWord_zero {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 0=Function.update R i 0 := by sorry
