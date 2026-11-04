-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_one
-- name    : ThreeSum.WeightedBankStageModel.lowerWord_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:57.415205+00:00
-- url     : https://prove2.me/theorems/a2b46b8d-0d2f-480f-a5fe-d092f2091e84
-- title:
--   Weighted Bank Stage Model: lower Word one
-- statement:
--   The Weighted Bank Stage Model construction uses the lower Word one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L41-L42

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

theorem ThreeSum.WeightedBankStageModel.lowerWord_one {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 1=Function.update R i (clampOne (R i)) := by sorry
