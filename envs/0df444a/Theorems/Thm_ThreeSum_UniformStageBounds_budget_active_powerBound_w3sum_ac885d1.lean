-- Prove2me | Theorems.Thm_ThreeSum_UniformStageBounds_budget_active_powerBound_w3sum_ac885d1
-- name    : ThreeSum.UniformStageBounds.budget_active_powerBound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:19.771039+00:00
-- url     : https://prove2.me/theorems/b0e2412b-01e7-47e6-a625-5f2f1cb3198a
-- title:
--   Uniform Stage Bounds: budget active power Bound
-- statement:
--   The Uniform Stage Bounds construction uses the budget active power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L62-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L62-L78

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

theorem ThreeSum.UniformStageBounds.budget_active_powerBound_w3sum_ac885d1 (k : ℕ) :
    PowerBound (activeCount (falseBudget k))
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by sorry
