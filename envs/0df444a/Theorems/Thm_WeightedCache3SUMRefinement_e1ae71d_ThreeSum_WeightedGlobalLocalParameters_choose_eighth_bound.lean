-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_choose_eighth_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.choose_eighth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:26.062826+00:00
-- url     : https://prove2.me/theorems/13d46b8d-0a62-46e9-84a1-cf782fb16de8
-- title:
--   choose_eighth_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L32-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L32-L56

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.choose_eighth_bound (m k : ℕ) (hk : k ≤ 8*m) :
    (8*m).choose k ≤ 2^(m+4*k) := by sorry
