-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:04:18.046533+00:00
-- url     : https://prove2.me/theorems/0664ed4d-7acf-4d4c-a817-3b584a06976b
-- title:
--   deficit_schedule
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/DimensionBounds.lean#L17-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/DimensionBounds.lean#L17-L18

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule (m j : ℕ) : queryDeficit m j=WeightedSchedule.treeBudget (j*m) := by sorry
