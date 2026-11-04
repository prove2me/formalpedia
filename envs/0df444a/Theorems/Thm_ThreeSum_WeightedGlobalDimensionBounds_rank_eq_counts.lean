-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_rank_eq_counts
-- name    : ThreeSum.WeightedGlobalDimensionBounds.rank_eq_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:47:51.319493+00:00
-- url     : https://prove2.me/theorems/68d5d885-52ff-4ac4-970d-8181e9ba64e9
-- title:
--   Weighted Global Dimension Bounds: rank eq counts
-- statement:
--   The Weighted Global Dimension Bounds construction uses the rank eq counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L29-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L29-L30

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.rank_eq_counts {N : ℕ} (Q : TritWord N) : rank Q=digitCount Q 1+2*digitCount Q 2 := by sorry
