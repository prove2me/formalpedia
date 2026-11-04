-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec
-- name    : ThreeSum.WeightedBankStageModel.index_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:02.692001+00:00
-- url     : https://prove2.me/theorems/9aef3c5f-b2ff-49f7-a02a-ceffd59422e1
-- title:
--   Weighted Bank Stage Model: index spec
-- statement:
--   The Weighted Bank Stage Model construction uses the index spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L53-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L53-L58

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

theorem ThreeSum.WeightedBankStageModel.index_spec {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by sorry
