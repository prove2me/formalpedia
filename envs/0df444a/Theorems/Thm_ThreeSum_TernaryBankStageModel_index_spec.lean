-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_index_spec
-- name    : ThreeSum.TernaryBankStageModel.index_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:25.93039+00:00
-- url     : https://prove2.me/theorems/c236897c-444d-40d4-91f8-fbd4bc073de7
-- title:
--   Ternary Bank Stage Model: index spec
-- statement:
--   The Ternary Bank Stage Model construction uses the index spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L47-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L47-L52

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

theorem ThreeSum.TernaryBankStageModel.index_spec {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by sorry
