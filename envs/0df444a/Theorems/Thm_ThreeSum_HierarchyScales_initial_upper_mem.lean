-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_initial_upper_mem
-- name    : ThreeSum.HierarchyScales.initial_upper_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:23.285484+00:00
-- url     : https://prove2.me/theorems/7ea98e71-badd-46c8-90ca-1cc9a3ec2080
-- title:
--   Hierarchy Scales: initial upper mem
-- statement:
--   The Hierarchy Scales construction uses the initial upper mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L190-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L190-L197

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.initial_upper_mem {n : ℕ} (hmu : 50 ≤ mu n) :
    initialTheta + 1 / (mu n : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by sorry
