-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_index_one_code
-- name    : ThreeSum.WeightedBankStageModel.index_one_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:28.321978+00:00
-- url     : https://prove2.me/theorems/5e746156-45ce-4a2e-9db2-c461ade02076
-- title:
--   Weighted Bank Stage Model: index one code
-- statement:
--   The Weighted Bank Stage Model construction uses the index one code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L71-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L71-L75

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedBankStageModel.index_one_code {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) :
    address (E.word (index E i 1 j))=
      LightTernaryCodes.oneCode (2*N) (high i) (address (E.word j)) := by sorry
