-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_moment_abs_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.moment_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:20:19.872214+00:00
-- url     : https://prove2.me/theorems/38632597-c335-485b-bfa9-3020575bf8f2
-- title:
--   moment_abs_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L76-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L76-L102

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.moment_abs_le {N U K k : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (i : ℕ) (hk : k≤K)
    (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ)) (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    |∑ p : Pair S i, mass S i p*mode B C p^k|≤(momentBound S U K : ℤ) := by sorry
