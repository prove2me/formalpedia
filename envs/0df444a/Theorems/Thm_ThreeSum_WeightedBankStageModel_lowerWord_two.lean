-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_two
-- name    : ThreeSum.WeightedBankStageModel.lowerWord_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:05.802205+00:00
-- url     : https://prove2.me/theorems/e26e58f8-a522-461c-8bb5-65f1a1bf2992
-- title:
--   Weighted Bank Stage Model: lower Word two
-- statement:
--   The Weighted Bank Stage Model construction uses the lower Word two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L44-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L44-L46

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedBankStageModel.lowerWord_two {N : ℕ} (R : TritWord N) (i : Fin N) : lowerWord R i 2=R := by sorry
