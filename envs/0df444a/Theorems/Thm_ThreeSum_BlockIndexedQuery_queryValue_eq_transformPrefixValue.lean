-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_queryValue_eq_transformPrefixValue
-- name    : ThreeSum.BlockIndexedQuery.queryValue_eq_transformPrefixValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:16.804059+00:00
-- url     : https://prove2.me/theorems/b5cf7fa1-1fe9-4f15-b76e-b9a73e40e516
-- title:
--   Block Indexed Query: query Value eq transform Prefix Value
-- statement:
--   The Block Indexed Query construction uses the query Value eq transform Prefix Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L172-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L172-L179

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

theorem ThreeSum.BlockIndexedQuery.queryValue_eq_transformPrefixValue {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J) :
    queryValue P d B C b c q k u =
      transformPrefixValue P d B C b c q (prefixIndices J k) u := by sorry
