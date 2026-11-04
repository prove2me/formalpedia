-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchCosts_word_le_budget
-- name    : ThreeSum.LightSwitchCosts.word_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:30:32.694962+00:00
-- url     : https://prove2.me/theorems/b298b8ad-2b64-4d34-86b6-fa39f2bfaf9c
-- title:
--   Light Switch Costs: word le budget
-- statement:
--   The Light Switch Costs construction uses the word le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L36-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean#L36-L40

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology

theorem ThreeSum.LightSwitchCosts.word_le_budget (n j : ℕ) :
    LightSwitch.word (blockCount (inputBits n)) (Switch.residualSize n j) ≤ wordBudget n := by sorry
