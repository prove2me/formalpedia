-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_initialCap_bounds
-- name    : ThreeSum.HierarchyScales.initialCap_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:09.437673+00:00
-- url     : https://prove2.me/theorems/507d2d01-2a71-4fb6-bdc4-79a8e3e275df
-- title:
--   Hierarchy Scales: initial Cap bounds
-- statement:
--   The Hierarchy Scales construction uses the initial Cap bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L23-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L23-L29

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.HierarchyScales.initialCap_bounds (r : ℕ) : r ≤ 25 * initialCap r ∧ 25 * initialCap r < r + 25 := by sorry
