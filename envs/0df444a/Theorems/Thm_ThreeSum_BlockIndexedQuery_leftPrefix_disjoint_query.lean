-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_disjoint_query
-- name    : ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:29.498292+00:00
-- url     : https://prove2.me/theorems/80ea3d14-67b9-4ccf-84cb-75444ab55ca5
-- title:
--   Block Indexed Query: left Prefix disjoint query
-- statement:
--   The Block Indexed Query construction uses the left Prefix disjoint query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L62-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L62-L64

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

theorem ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (leftPrefix k u) (querySet k Q) := by sorry
