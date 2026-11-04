-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_initial_query_eventually_le_w3sum_ac885d1
-- name    : ThreeSum.HierarchyScales.initial_query_eventually_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:17.775164+00:00
-- url     : https://prove2.me/theorems/6eb52779-1b01-4b95-a0ac-01c42e55455e
-- title:
--   Hierarchy Scales: initial query eventually le
-- statement:
--   The Hierarchy Scales construction uses the initial query eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L235-L255
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L235-L255

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.initial_query_eventually_le_w3sum_ac885d1 {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (queryTerms n 0 : ℝ) ≤
      (n : ℝ) ^ (entropy initialTheta / 5 + d) := by sorry
