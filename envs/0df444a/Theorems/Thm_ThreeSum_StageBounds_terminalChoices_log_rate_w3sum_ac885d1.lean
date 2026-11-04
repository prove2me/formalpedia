-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_terminalChoices_log_rate_w3sum_ac885d1
-- name    : ThreeSum.StageBounds.terminalChoices_log_rate_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:00.482811+00:00
-- url     : https://prove2.me/theorems/37096754-37b7-4acf-8f2d-259f2f33b6f8
-- title:
--   Stage Bounds: terminal Choices log rate
-- statement:
--   The Stage Bounds construction uses the terminal Choices log rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L177-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L177-L190

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.StageBounds.terminalChoices_log_rate_w3sum_ac885d1 :
    Tendsto (fun n : ℕ => Real.log (terminalChoices n : ℝ) / Real.log n) atTop
      (𝓝 ((1 - terminalFraction) / 5)) := by sorry
