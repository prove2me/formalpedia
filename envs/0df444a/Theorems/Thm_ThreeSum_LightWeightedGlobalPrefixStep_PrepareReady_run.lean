-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
-- name    : ThreeSum.LightWeightedGlobalPrefixStep.PrepareReady.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:55:46.427095+00:00
-- url     : https://prove2.me/theorems/3cce0881-70ac-41cc-834f-2337c3ab2a1d
-- title:
--   Prepare Ready: run
-- statement:
--   The Prepare Ready construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixStep.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixStep.lean#L90-L97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixStep
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixStep.PrepareReady.run {X : Inputs} {lim : Limits} {P : Program} {depth : ℕ} {μ : ℕ→ℤ}
    (H : PrepareReady X lim depth μ) (L : Library P) :
    Meets lim P 196 depth X.argv μ (LightWeightedGlobalPrefixPrepare.time X.m X.j X.alpha2)
      (fun r ν=>r=((X.power*X.p:ℕ):ℤ) ∧ Prepared X μ ν) := by sorry
