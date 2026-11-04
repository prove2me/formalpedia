-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_index_suffixDomain_w3sum_ac885d1
-- name    : ThreeSum.BlockIndexedQuery.index_suffixDomain_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:04.762984+00:00
-- url     : https://prove2.me/theorems/1f8175f5-9753-437e-a97f-b866cd2a6d6c
-- title:
--   Block Indexed Query: index suffix Domain
-- statement:
--   The Block Indexed Query construction uses the index suffix Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L33-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L33-L51

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

theorem ThreeSum.BlockIndexedQuery.index_suffixDomain_w3sum_ac885d1 {J L k : ℕ} (hk : k ≤ J) :
    indexSet (suffixDomain (L := L) (prefixIndices J k)) =
      SubsetStages.suffix (J*L) (suffixStage J L k) := by sorry
