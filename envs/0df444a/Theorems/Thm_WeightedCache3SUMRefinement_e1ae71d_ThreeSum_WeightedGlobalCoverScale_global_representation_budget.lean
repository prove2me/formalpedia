-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_global_representation_budget
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.global_representation_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:24:29.79959+00:00
-- url     : https://prove2.me/theorems/b5340b82-a0c6-443a-bac9-1bb007c2cc7d
-- title:
--   global_representation_budget
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverScale.lean#L235-L252
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverScale.lean#L235-L252

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.global_representation_budget (c d a n r : ℕ)
    (hradix : prime (scale 40000000000 c d)^r ≤ a*n^3) (han : a ≤ n) :
    ((localFactor 40000000000 c d)^r : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by sorry
