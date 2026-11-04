-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_AppendGuard_runB
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:18:59.007805+00:00
-- url     : https://prove2.me/theorems/7edae1f4-900c-43e6-bd04-dd34f4901a0a
-- title:
--   Append Guard: run B
-- statement:
--   The Append Guard construction uses the run B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L171-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L171-L181

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

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.AppendGuard.runB {C : Config} {D : Data C} {depth : ℕ} {μ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Bmatrix,C.row,C.Bold,C.Bnew,C.nB,C.J+2,C.p,C.power,C.hashWork] μ
      (LightTernaryAppendKeys.time C.nB (C.J+2) C.p D.bB)
      (fun _ ν => BuiltB C D μ ν) := by sorry
