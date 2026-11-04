-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_cut_schedule
-- name    : ThreeSum.WeightedGlobalDimensionBounds.cut_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:47:43.89594+00:00
-- url     : https://prove2.me/theorems/665ed896-ca15-43b6-b7a9-2daf64ed3a65
-- title:
--   Weighted Global Dimension Bounds: cut schedule
-- statement:
--   The Weighted Global Dimension Bounds construction uses the cut schedule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L15-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L15-L16

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.cut_schedule (m j : ℕ) : bankCut m j=WeightedSchedule.bankCut (j*m) := by sorry
