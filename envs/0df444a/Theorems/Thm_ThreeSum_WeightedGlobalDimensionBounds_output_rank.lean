-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_output_rank
-- name    : ThreeSum.WeightedGlobalDimensionBounds.output_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:49:13.738458+00:00
-- url     : https://prove2.me/theorems/188e630e-f090-44cc-8d82-5650781f525a
-- title:
--   Weighted Global Dimension Bounds: output rank
-- statement:
--   The Weighted Global Dimension Bounds construction uses the output rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L34-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L34-L37

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedSchedule_output_rank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.output_rank {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q=6516487530000*j*m := by sorry
