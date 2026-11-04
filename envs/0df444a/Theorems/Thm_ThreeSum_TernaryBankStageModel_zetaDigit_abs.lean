-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankStageModel_zetaDigit_abs
-- name    : ThreeSum.TernaryBankStageModel.zetaDigit_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:00.689888+00:00
-- url     : https://prove2.me/theorems/76bee8f8-9cbd-4f0e-b29f-1f1b669f29e9
-- title:
--   Ternary Bank Stage Model: zeta Digit abs
-- statement:
--   The Ternary Bank Stage Model construction uses the zeta Digit abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L86-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean#L86-L97

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

theorem ThreeSum.TernaryBankStageModel.zetaDigit_abs (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |zetaDigit f q|≤4*B := by sorry
