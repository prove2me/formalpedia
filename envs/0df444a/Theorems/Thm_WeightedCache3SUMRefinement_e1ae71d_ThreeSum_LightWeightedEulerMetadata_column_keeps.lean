-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_column_keeps
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.column_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:00.11319+00:00
-- url     : https://prove2.me/theorems/400070b0-75aa-4c63-afa6-91db680c984d
-- title:
--   column_keeps
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L31-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L31-L39

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.column_keeps {μ ν : ℕ → ℤ} {ws N rows i k : ℕ}
    (hi : i<N) (hk : k<N) (hne : i≠k)
    (H : LightWeightedPredecessorTable.KeptApart μ ν (ws+k) N rows) (j : ℕ) :
    ν (rowAddr ws N i j)=μ (rowAddr ws N i j) := by sorry
