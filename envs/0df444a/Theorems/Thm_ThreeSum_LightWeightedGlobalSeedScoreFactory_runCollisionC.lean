-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_runCollisionC
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.runCollisionC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:14:33.787548+00:00
-- url     : https://prove2.me/theorems/2dcb0752-09a6-4879-b93b-1c39482195c6
-- title:
--   Light Weighted Global Seed Score Factory: run Collision C
-- statement:
--   The Light Weighted Global Seed Score Factory construction uses the run Collision C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L344-L360
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L344-L360

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

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.runCollisionC {C : Config} [Fact C.p.Prime] {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (X : CollisionGuard C D lim R S raws words maps) (H : Built C D R S raws words maps μ ν) :
    Meets lim LightOriginalCollisionScore.program 0 (depth+1) [C.Cnew,C.nC,C.hist,C.power*C.p] ν
      (LightOriginalCollisionScore.time C.nC (C.power*C.p))
      (fun r ξ => r=D.collisionC ∧ Built C D R S raws words maps μ ξ) := by sorry
