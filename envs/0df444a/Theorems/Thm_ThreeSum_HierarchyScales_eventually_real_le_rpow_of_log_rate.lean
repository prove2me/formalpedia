-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_eventually_real_le_rpow_of_log_rate
-- name    : ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:10.482194+00:00
-- url     : https://prove2.me/theorems/1ee09815-0948-467f-82b8-1cdb92c637ba
-- title:
--   Hierarchy Scales: eventually real le rpow of log rate
-- statement:
--   The Hierarchy Scales construction uses the eventually real le rpow of log rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L129-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L129-L136

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by sorry
