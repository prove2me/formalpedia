-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
-- name    : ThreeSum.StageBounds.PowerBound.of_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:08.196927+00:00
-- url     : https://prove2.me/theorems/0f3b92b7-c3bf-4ce1-8caf-32140c64a1e4
-- title:
--   Power Bound: of rate
-- statement:
--   The Power Bound construction uses the of rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L56-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L56-L58

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
open ThreeSum.StageBounds.PowerBound

theorem ThreeSum.StageBounds.PowerBound.of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : PowerBound f a := by sorry
