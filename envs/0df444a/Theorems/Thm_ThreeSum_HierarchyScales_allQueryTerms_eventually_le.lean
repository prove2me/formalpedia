-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_allQueryTerms_eventually_le
-- name    : ThreeSum.HierarchyScales.allQueryTerms_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:14:26.25929+00:00
-- url     : https://prove2.me/theorems/3cc1d8bf-1351-4c51-ba42-4125fad2ca37
-- title:
--   Hierarchy Scales: all Query Terms eventually le
-- statement:
--   The Hierarchy Scales construction uses the all Query Terms eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L146-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L146-L153

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.allQueryTerms_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allQueryTerms n : ℝ) ≤
      (n : ℝ) ^ ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 + d) := by sorry
