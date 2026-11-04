-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_queryValue_eq_bucket_sum
-- name    : ThreeSum.BlockIndexedQuery.queryValue_eq_bucket_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:45.796367+00:00
-- url     : https://prove2.me/theorems/c5b346a2-b191-401d-8295-cd2d6c803fb0
-- title:
--   Block Indexed Query: query Value eq bucket sum
-- statement:
--   The Block Indexed Query construction uses the query Value eq bucket sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L181-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L181-L189

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.BlockIndexedQuery.queryValue_eq_bucket_sum {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ outputRows q i ∧ (u i).card = h) :
    queryValue P d B C b c q k u =
      (∑ t ∈ completedTuples q (prefixIndices J k) u,
        leftBucket P B b t * rightBucket P d C c t : ℕ) := by sorry
