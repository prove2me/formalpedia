-- Prove2me | Theorems.Thm_ThreeSum_ArithmeticStageBounds_rounded_maxMod_powerBound
-- name    : ThreeSum.ArithmeticStageBounds.rounded_maxMod_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:44:23.34107+00:00
-- url     : https://prove2.me/theorems/7d515496-5e39-49c3-b418-24aa5c8b3eb2
-- title:
--   Arithmetic Stage Bounds: rounded max Mod power Bound
-- statement:
--   The Arithmetic Stage Bounds construction uses the rounded max Mod power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L115-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L115-L119

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
noncomputable section

theorem ThreeSum.ArithmeticStageBounds.rounded_maxMod_powerBound :
    PowerBound (fun n => roundedPower (maxMod n)) ((8/5)*((E+1/2)/5)) := by sorry
