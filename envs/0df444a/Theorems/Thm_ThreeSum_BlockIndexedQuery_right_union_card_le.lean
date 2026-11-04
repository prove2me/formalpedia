-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_right_union_card_le
-- name    : ThreeSum.BlockIndexedQuery.right_union_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:12.149739+00:00
-- url     : https://prove2.me/theorems/483143af-5f47-4d8b-b162-ede133ab5429
-- title:
--   Block Indexed Query: right union card le
-- statement:
--   The Block Indexed Query construction uses the right union card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L110-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L110-L116

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

theorem ThreeSum.BlockIndexedQuery.right_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (rightPrefix k Q u ∪ querySet k Q).card ≤ 2*h*J := by sorry
