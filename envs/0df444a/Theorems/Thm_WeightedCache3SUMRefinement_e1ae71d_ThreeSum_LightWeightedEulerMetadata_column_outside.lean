-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_column_outside
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.column_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:11:56.87033+00:00
-- url     : https://prove2.me/theorems/6bca411d-e4e4-4b7c-8f9d-2f36af47210b
-- title:
--   column_outside
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L41-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L41-L50

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.column_outside {μ ν : ℕ → ℤ} {ws N rows k : ℕ} (hk : k<N)
    (H : LightWeightedPredecessorTable.KeptApart μ ν (ws+k) N rows) :
    SameOutside μ ν ws (2*N*rows) := by sorry
