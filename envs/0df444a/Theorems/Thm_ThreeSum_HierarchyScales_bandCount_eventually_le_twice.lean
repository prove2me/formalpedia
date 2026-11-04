-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_bandCount_eventually_le_twice
-- name    : ThreeSum.HierarchyScales.bandCount_eventually_le_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:28.08318+00:00
-- url     : https://prove2.me/theorems/f4ebd89c-9c43-40c2-b035-8f6f46ceaf8e
-- title:
--   Hierarchy Scales: band Count eventually le twice
-- statement:
--   The Hierarchy Scales construction uses the band Count eventually le twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L297-L309
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L297-L309

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.bandCount_eventually_le_twice :
    ∀ᶠ n : ℕ in atTop, (bandCount n : ℝ) ≤ 2 * unroundedBandCount n := by sorry
