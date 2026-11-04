-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_zero
-- name    : ThreeSum.TernaryBankStageModel.lowerWord_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:44.659765+00:00
-- url     : https://prove2.me/theorems/e24c0852-80c5-4cf2-b953-ecf3ebad7bed
-- title:
--   Ternary Bank Stage Model: lower Word zero
-- statement:
--   The Ternary Bank Stage Model construction uses the lower Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L27-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L27-L30

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

theorem ThreeSum.TernaryBankStageModel.lowerWord_zero {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 0=Function.update R i 0 := by sorry
