-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_owner_count_powerBound
-- name    : ThreeSum.BandPrimeCosts.owner_count_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:32.857432+00:00
-- url     : https://prove2.me/theorems/91492940-69fa-4126-b6e9-a2c839a093dd
-- title:
--   Band Prime Costs: owner count power Bound
-- statement:
--   The Band Prime Costs construction uses the owner count power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCostBounds.lean#L43-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCostBounds.lean#L43-L52

import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section

theorem ThreeSum.BandPrimeCosts.owner_count_powerBound :
    PowerBound (fun n => 3*bandCount n^2+1) (2*(1-(E+bandShift)/5)) := by sorry
