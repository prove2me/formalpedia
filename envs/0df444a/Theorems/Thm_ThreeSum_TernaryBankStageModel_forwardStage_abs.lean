-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_abs
-- name    : ThreeSum.TernaryBankStageModel.forwardStage_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:53.59319+00:00
-- url     : https://prove2.me/theorems/05b02236-73a2-4c52-b1d3-8bd2f9f0dcc9
-- title:
--   Ternary Bank Stage Model: forward Stage abs
-- statement:
--   The Ternary Bank Stage Model construction uses the forward Stage abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L99-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L99-L109

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

theorem ThreeSum.TernaryBankStageModel.forwardStage_abs {N : ℕ} (K : ℕ) (hK : K≤N) (F : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage K F R|≤((4^K : ℕ) : ℤ)*(V : ℤ) := by sorry
