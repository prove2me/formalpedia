-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_two
-- name    : ThreeSum.TernaryBankStageModel.lowerWord_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:29.498067+00:00
-- url     : https://prove2.me/theorems/035f2e7d-3dd5-4200-ba8b-391e216688ea
-- title:
--   Ternary Bank Stage Model: lower Word two
-- statement:
--   The Ternary Bank Stage Model construction uses the lower Word two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L38-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L38-L40

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryBankStageModel.lowerWord_two {N : ℕ} (R : TritWord N) (i : Fin N) : lowerWord R i 2=R := by sorry
