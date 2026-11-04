-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_AppendGuard_runO
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:19:05.095548+00:00
-- url     : https://prove2.me/theorems/83774a86-4204-4046-96ff-50d2fd904ed1
-- title:
--   Append Guard: run O
-- statement:
--   The Append Guard construction uses the run O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L203-L224
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L203-L224

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runO {C : Config} {D : Data C} {depth : ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : BuiltC C D μ ν) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Omatrix,C.row,C.Oold,C.Onew,C.nO,C.J+2,C.p,C.power,C.hashWork] ν
      (LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO)
      (fun _ ξ => BuiltO C D μ ξ) := by sorry
