-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
-- name    : ThreeSum.StageBounds.PowerBound.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:14:54.642673+00:00
-- url     : https://prove2.me/theorems/0400b0c8-a536-4a4e-90c1-a2d303df26b2
-- title:
--   Power Bound: mul
-- statement:
--   The Power Bound construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L62-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L62-L72

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

theorem ThreeSum.StageBounds.PowerBound.mul {f g : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hg : PowerBound g b) :
    PowerBound (fun n => f n * g n) (a + b) := by sorry
