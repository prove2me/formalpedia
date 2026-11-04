-- Prove2me | Theorems.Thm_ThreeSum_UniformStageBounds_budget_terminal_powerBound
-- name    : ThreeSum.UniformStageBounds.budget_terminal_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:13.483865+00:00
-- url     : https://prove2.me/theorems/470008b0-7c55-4c42-abd0-74f8ae67172f
-- title:
--   Uniform Stage Bounds: budget terminal power Bound
-- statement:
--   The Uniform Stage Bounds construction uses the budget terminal power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L80-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L80-L89

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.UniformStageBounds.budget_terminal_powerBound (k : ℕ) :
    PowerBound (terminalCount (falseBudget k))
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by sorry
