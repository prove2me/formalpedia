-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixedPi_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:50.525601+00:00
-- url     : https://prove2.me/theorems/41f5596b-14f4-44f1-9cd6-519cee07a09c
-- title:
--   fixedPi_space
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L23-L25

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixedPi_space (m : ℕ) : 2*(fixedPi m 1)+3*(fixedPi m 2) ≤ fixedLength m := by sorry
