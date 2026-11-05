-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixed_thirds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixed_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:25.187206+00:00
-- url     : https://prove2.me/theorems/cdf04274-f84d-4956-9428-3df87ad96fe6
-- title:
--   fixed_thirds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L27-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L27-L29

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixed_thirds (m : ℕ) : fixedPi m 2 = 3*(fixedAlpha m 2) := by sorry
