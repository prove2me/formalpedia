-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_querySet_card
-- name    : ThreeSum.BlockIndexedQuery.querySet_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:13.830667+00:00
-- url     : https://prove2.me/theorems/cc2c6f76-7846-4375-9015-d16ae9eedf07
-- title:
--   Block Indexed Query: query Set card
-- statement:
--   The Block Indexed Query construction uses the query Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L90-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L90-L93

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

theorem ThreeSum.BlockIndexedQuery.querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (querySet k Q).card = (J-k)*(2*h) := by sorry
