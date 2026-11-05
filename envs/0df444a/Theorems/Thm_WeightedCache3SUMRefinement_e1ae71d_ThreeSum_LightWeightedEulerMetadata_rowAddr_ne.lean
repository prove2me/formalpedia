-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_rowAddr_ne
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.rowAddr_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:04.914534+00:00
-- url     : https://prove2.me/theorems/09f2337f-5baf-48ed-8281-bc920e00014d
-- title:
--   rowAddr_ne
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EulerMetadata.lean#L22-L29

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.rowAddr_ne {ws N i k j l : ℕ} (hi : i<N) (hk : k<N) (hne : i≠k) :
    rowAddr ws N i j≠rowAddr ws N k l := by sorry
