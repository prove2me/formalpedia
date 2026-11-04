-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_allPrefixBoxes_eventually_le
-- name    : ThreeSum.HierarchyScales.allPrefixBoxes_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:11.61909+00:00
-- url     : https://prove2.me/theorems/30355537-b607-4c9a-991a-c78316cefd95
-- title:
--   Hierarchy Scales: all Prefix Boxes eventually le
-- statement:
--   The Hierarchy Scales construction uses the all Prefix Boxes eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L138-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L138-L144

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.allPrefixBoxes_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allPrefixBoxes n : ℝ) ≤
      (n : ℝ) ^ ((2 * E + 2 * bandShift - boxSaving) / 5 + d) := by sorry
