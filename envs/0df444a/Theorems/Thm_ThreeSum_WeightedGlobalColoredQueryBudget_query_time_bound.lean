-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredQueryBudget_query_time_bound
-- name    : ThreeSum.WeightedGlobalColoredQueryBudget.query_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:15:22.067961+00:00
-- url     : https://prove2.me/theorems/6aec9a2c-3aba-40a4-ae5c-cf00fbbad652
-- title:
--   Weighted Global Colored Query Budget: query time bound
-- statement:
--   The single time value used by the real loop is bounded uniformly in
--   all source values, normalized lengths, free pointers and runtime fields.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredQueryBudget.lean#L24-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredQueryBudget.lean#L24-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredQueryBudget
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredQueryBudget.query_time_bound (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hn : 1<n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    (queryTime P n free A B C:ℝ)≤
      (coefficient P:ℝ)*(J P n+1:ℕ)^3*
        WeightedGlobalCountFrontendBudget.envelope P.m (rounds P n) := by sorry
