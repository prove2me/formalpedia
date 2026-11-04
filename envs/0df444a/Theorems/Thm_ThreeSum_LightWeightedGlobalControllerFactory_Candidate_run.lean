-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
-- name    : ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:19:38.938782+00:00
-- url     : https://prove2.me/theorems/eb0266d5-e81d-453c-a930-1472fd6db4f7
-- title:
--   Candidate: run
-- statement:
--   The Candidate construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L58-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L58-L76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run {C : Config} [Fact C.p.Prime] {D : Candidate C} {lim : Limits}
    {depth K R S : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (G : D.Guard lim depth K R S raws words maps μ) :
    Meets lim (LightWeightedGlobalSeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      176 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ D.Done K μ ν) := by sorry
