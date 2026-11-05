-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.mem_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:28:01.364314+00:00
-- url     : https://prove2.me/theorems/c758ae7d-dbf3-4787-b385-617f45883d0e
-- title:
--   mem_pair
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L16-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L16-L25

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.mem_pair {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (i b c j k : ℕ) : ((b,j),(c,k))∈pairs S i ↔
      (b,j)∈S.left.records ∧ S.left.group j=S.front.group i ∧
      (c,k)∈S.right.records ∧ S.right.group k=S.front.group i ∧
      TernaryConvolution.Adds (S.front.E.word (S.left.key j))
        (S.front.E.word (S.right.key k)) (S.front.Q i) := by sorry
