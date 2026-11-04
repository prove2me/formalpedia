-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_card
-- name    : ThreeSum.BlockIndexedQuery.leftPrefix_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:23.280225+00:00
-- url     : https://prove2.me/theorems/2f1383b1-47be-4f8d-8278-e506d017754c
-- title:
--   Block Indexed Query: left Prefix card
-- statement:
--   The Block Indexed Query construction uses the left Prefix card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L76-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L76-L78

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

theorem ThreeSum.BlockIndexedQuery.leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) : (leftPrefix k u).card = k*h := by sorry
