-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_runWanted
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.runWanted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:22:38.379314+00:00
-- url     : https://prove2.me/theorems/19c998f0-1c15-4072-9664-e487c7a665a7
-- title:
--   Light Weighted Global Seed Score Factory: run Wanted
-- statement:
--   The Light Weighted Global Seed Score Factory construction uses the run Wanted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L284-L308
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L284-L308

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.runWanted {C : Config} {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (H : BuiltO C D μ ν) :
    Meets lim (LightTernaryWantedBatch.program C.p R S raws words maps) 4 (depth+1)
      [C.prefixLength,C.Onew,C.positions,C.nO,C.wanted,C.work] ν
      (LightTernaryWantedBatch.time C.p cap V C.prefixLength C.nO)
      (fun r ξ => r=((C.wanted+3*D.H R S raws words maps : ℕ) : ℤ) ∧ Built C D R S raws words maps μ ξ) := by sorry
