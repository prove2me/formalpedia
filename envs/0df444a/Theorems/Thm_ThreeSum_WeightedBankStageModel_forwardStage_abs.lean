-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_abs
-- name    : ThreeSum.WeightedBankStageModel.forwardStage_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:22.929199+00:00
-- url     : https://prove2.me/theorems/9aa7e318-6c72-451f-b502-847cf9b5fae8
-- title:
--   Weighted Bank Stage Model: forward Stage abs
-- statement:
--   The Weighted Bank Stage Model construction uses the forward Stage abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L105-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L105-L115

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

theorem ThreeSum.WeightedBankStageModel.forwardStage_abs {N : ℕ} (K : ℕ) (hK : K≤N) (F : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage K F R|≤((4^K : ℕ) : ℤ)*(V : ℤ) := by sorry
