-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_initial_query_log_bound
-- name    : ThreeSum.HierarchyScales.initial_query_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:17.204203+00:00
-- url     : https://prove2.me/theorems/7fd3479a-31d5-435d-bd31-f40c3d0d9763
-- title:
--   Hierarchy Scales: initial query log bound
-- statement:
--   The Hierarchy Scales construction uses the initial query log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L199-L225
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L199-L225

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.initial_query_log_bound {n : ℕ} (hmu : 50 ≤ mu n) :
    Real.log (queryTerms n 0 : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) := by sorry
