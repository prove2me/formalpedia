-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_bandCount_ge_unrounded
-- name    : ThreeSum.HierarchyScales.bandCount_ge_unrounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:25.17621+00:00
-- url     : https://prove2.me/theorems/f19d4bd1-a74b-4444-9599-57617baf30b3
-- title:
--   Hierarchy Scales: band Count ge unrounded
-- statement:
--   The Hierarchy Scales construction uses the band Count ge unrounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L277-L282
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L277-L282

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.bandCount_ge_unrounded (n : ℕ) : unroundedBandCount n ≤ (bandCount n : ℝ) := by sorry
