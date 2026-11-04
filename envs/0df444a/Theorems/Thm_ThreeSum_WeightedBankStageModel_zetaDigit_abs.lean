-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_zetaDigit_abs
-- name    : ThreeSum.WeightedBankStageModel.zetaDigit_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:25.242866+00:00
-- url     : https://prove2.me/theorems/b6f25199-bbef-4a6b-a57d-9bb87b2ffe25
-- title:
--   Weighted Bank Stage Model: zeta Digit abs
-- statement:
--   The Weighted Bank Stage Model construction uses the zeta Digit abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L92-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L92-L103

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

theorem ThreeSum.WeightedBankStageModel.zetaDigit_abs (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |zetaDigit f q|≤4*B := by sorry
