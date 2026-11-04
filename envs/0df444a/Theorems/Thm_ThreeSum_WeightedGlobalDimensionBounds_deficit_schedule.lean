-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
-- name    : ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:37.475725+00:00
-- url     : https://prove2.me/theorems/bb11cc8c-2603-4f41-823e-9577abe39f23
-- title:
--   Weighted Global Dimension Bounds: deficit schedule
-- statement:
--   The Weighted Global Dimension Bounds construction uses the deficit schedule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L17-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L17-L18

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule (m j : ℕ) : queryDeficit m j=WeightedSchedule.treeBudget (j*m) := by sorry
