-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow
-- name    : ThreeSum.StageBounds.PowerBound.pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:04.322828+00:00
-- url     : https://prove2.me/theorems/f494c7c8-7077-4fd9-a83f-4dba84400143
-- title:
--   Power Bound: pow
-- statement:
--   The Power Bound construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L94-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L94-L99

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

theorem ThreeSum.StageBounds.PowerBound.pow {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (k : ℕ) :
    PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by sorry
