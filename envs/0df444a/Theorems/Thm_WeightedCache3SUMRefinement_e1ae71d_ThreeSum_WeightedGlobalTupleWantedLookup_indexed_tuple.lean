-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleWantedLookup_indexed_tuple
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup.indexed_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:36:37.114064+00:00
-- url     : https://prove2.me/theorems/9f3d2f30-e4c7-4ca2-b6da-3e48177e4c2b
-- title:
--   indexed_tuple
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L25-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L25-L45

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup.indexed_tuple {A : Type*} (base : List A) (xs : List A)
    (hx : ∀ x∈xs, x∈base) :
    ∃ is : List ℕ, is.length=xs.length ∧ (∀ i∈is, i<base.length) ∧
      ∀ (B : Type*) (raw : A→B) (fallback : B),
        is.map (fun i => (base.map raw).getD i fallback)=xs.map raw := by sorry
