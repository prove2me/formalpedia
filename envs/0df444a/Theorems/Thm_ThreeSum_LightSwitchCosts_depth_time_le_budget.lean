-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchCosts_depth_time_le_budget
-- name    : ThreeSum.LightSwitchCosts.depth_time_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:29:55.319517+00:00
-- url     : https://prove2.me/theorems/ebe88496-2fd7-4e00-a381-0b5b622a610a
-- title:
--   Light Switch Costs: depth time le budget
-- statement:
--   The Light Switch Costs construction uses the depth time le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L29-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L29-L34

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology

theorem ThreeSum.LightSwitchCosts.depth_time_le_budget (n : ℕ) :
    LightSwitchDepth.time (blockCount (inputBits n)) ≤ depthBudget n := by sorry
