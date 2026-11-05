-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixedPi_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:48.332083+00:00
-- url     : https://prove2.me/theorems/d096dab3-1f47-4a4a-b976-cb084a4f0250
-- title:
--   fixedPi_total
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L19-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean#L19-L21

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.fixedPi_total (m : ℕ) : fixedPi m 0+fixedPi m 1+fixedPi m 2 = fixedLength m := by sorry
