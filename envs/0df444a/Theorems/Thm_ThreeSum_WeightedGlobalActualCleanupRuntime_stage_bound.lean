-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualCleanupRuntime_stage_bound
-- name    : ThreeSum.WeightedGlobalActualCleanupRuntime.stage_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:26:54.149794+00:00
-- url     : https://prove2.me/theorems/74617529-fe06-4c70-bcd2-ced9b14f040c
-- title:
--   Weighted Global Actual Cleanup Runtime: stage bound
-- statement:
--   The Weighted Global Actual Cleanup Runtime construction uses the stage bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L19-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L19-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalActualCleanupRuntime.stage_bound (keys : ℕ→ℕ) (size scan L n : ℕ) (hs : size≤n) (hscan : scan≤n) :
    LightOriginalSurvivorStage.time keys size scan L≤
      280*n+720+collisions keys size*(n*(120*L+330)+300) := by sorry
