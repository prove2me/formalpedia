-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchCosts_all_time_le_budget
-- name    : ThreeSum.LightSwitchCosts.all_time_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:29:58.205328+00:00
-- url     : https://prove2.me/theorems/dd512e1d-d93e-452a-9651-1d5d7f1c7168
-- title:
--   Light Switch Costs: all time le budget
-- statement:
--   The Light Switch Costs construction uses the all time le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L50-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L50-L66

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology

theorem ThreeSum.LightSwitchCosts.all_time_le_budget (n : ℕ) :
    LightSwitchDepth.time (blockCount (inputBits n))+
      (∑ j ∈ Finset.range (Switch.terminalDepth n+1), LightSwitch.time (Switch.residualSize n j)) ≤
        allTimeBudget n := by sorry
