-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
-- name    : ThreeSum.LightWeightedGlobalPrefixPhases.Phase.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:28.25195+00:00
-- url     : https://prove2.me/theorems/8a87e2c6-f0c2-4d34-b213-c7d07a7aa12e
-- title:
--   Phase: run
-- statement:
--   The Phase construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L64-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L64-L74

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPhases
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixPhases
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [instance] Phase.prime

theorem ThreeSum.LightWeightedGlobalPrefixPhases.Phase.run {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 192 depth X.argv μ H.time
      (fun z ω=>z=((X.power*X.p:ℕ):ℤ) ∧ H.Output ω) := by sorry
