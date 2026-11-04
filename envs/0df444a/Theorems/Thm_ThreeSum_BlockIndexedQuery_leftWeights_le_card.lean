-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_leftWeights_le_card
-- name    : ThreeSum.BlockIndexedQuery.leftWeights_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:17.014825+00:00
-- url     : https://prove2.me/theorems/fe8cc285-5892-4365-bec4-5649e89de243
-- title:
--   Block Indexed Query: left Weights le card
-- statement:
--   The Block Indexed Query construction uses the left Weights le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L132-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L132-L140

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

theorem ThreeSum.BlockIndexedQuery.leftWeights_le_card {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512*h))) :
    leftWeights o P B b S ≤ B.card := by sorry
