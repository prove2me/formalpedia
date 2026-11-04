-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_one
-- name    : ThreeSum.TernaryBankStageModel.lowerWord_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:56.133792+00:00
-- url     : https://prove2.me/theorems/e7556267-475a-407f-889a-ee8aac5d4e1d
-- title:
--   Ternary Bank Stage Model: lower Word one
-- statement:
--   The Ternary Bank Stage Model construction uses the lower Word one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L35-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L35-L36

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryBankStageModel.lowerWord_one {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 1=Function.update R i (clampOne (R i)) := by sorry
