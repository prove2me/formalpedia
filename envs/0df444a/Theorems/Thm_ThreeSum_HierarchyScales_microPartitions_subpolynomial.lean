-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_microPartitions_subpolynomial
-- name    : ThreeSum.HierarchyScales.microPartitions_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:14:28.228502+00:00
-- url     : https://prove2.me/theorems/4b9fe780-5d5e-4950-94da-d3f2c195d933
-- title:
--   Hierarchy Scales: micro Partitions subpolynomial
-- statement:
--   The Hierarchy Scales construction uses the micro Partitions subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L166-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L166-L173

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.microPartitions_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (microPartitions n : ℝ) ≤ (n : ℝ) ^ d := by sorry
