-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
-- name    : ThreeSum.LightWeightedGlobalPrefixPhases.LoopPlan.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:52.91706+00:00
-- url     : https://prove2.me/theorems/6d2a1e6f-f46a-4f06-bd9a-52c59f9362e6
-- title:
--   Loop Plan: run
-- statement:
--   The Loop Plan construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L116-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L116-L124

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

theorem ThreeSum.LightWeightedGlobalPrefixPhases.LoopPlan.run {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ} {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : LoopPlan lim rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
      depth K R S T raws words maps xl yl zl xr yr zr μ) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 193 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale)
      μ (LightWeightedGlobalPrefixLoop.time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ H.invariant rounds ν) := by sorry
