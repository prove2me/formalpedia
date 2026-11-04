-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_of_le
-- name    : ThreeSum.TernaryBankStageModel.lowerWord_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:20.546231+00:00
-- url     : https://prove2.me/theorems/fcb241c6-0fd6-424c-8629-2590a0649d5a
-- title:
--   Ternary Bank Stage Model: lower Word of le
-- statement:
--   The Ternary Bank Stage Model construction uses the lower Word of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L24-L25

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

theorem ThreeSum.TernaryBankStageModel.lowerWord_of_le {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) (he : e≤R i) :
    lowerWord R i e=Function.update R i e := by sorry
