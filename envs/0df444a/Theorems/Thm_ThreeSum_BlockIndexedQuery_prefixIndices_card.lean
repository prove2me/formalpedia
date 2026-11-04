-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
-- name    : ThreeSum.BlockIndexedQuery.prefixIndices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:45.646464+00:00
-- url     : https://prove2.me/theorems/f0bc2147-3ad1-4af1-afb2-0d7dd626ac32
-- title:
--   Block Indexed Query: prefix Indices card
-- statement:
--   The Block Indexed Query construction uses the prefix Indices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L24-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L24-L26

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

theorem ThreeSum.BlockIndexedQuery.prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (prefixIndices J k).card = k := by sorry
