-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_AppendGuard_runC
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:19:02.620217+00:00
-- url     : https://prove2.me/theorems/87e6c204-5776-4b7c-94c5-b3aa4c3253a4
-- title:
--   Append Guard: run C
-- statement:
--   The Append Guard construction uses the run C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L183-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L183-L201

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

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runC {C : Config} {D : Data C} {depth : ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : BuiltB C D μ ν) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Cmatrix,C.row,C.Cold,C.Cnew,C.nC,C.J+2,C.p,C.power,C.hashWork] ν
      (LightTernaryAppendKeys.time C.nC (C.J+2) C.p D.bC)
      (fun _ ξ => BuiltC C D μ ξ) := by sorry
