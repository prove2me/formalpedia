-- Prove2me | Theorems.Thm_ThreeSum_BlockIndexedQuery_rightSource_abs_le
-- name    : ThreeSum.BlockIndexedQuery.rightSource_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:28.376202+00:00
-- url     : https://prove2.me/theorems/2d3a275e-832c-4dba-9730-f47fbde7b8ac
-- title:
--   Block Indexed Query: right Source abs le
-- statement:
--   The Block Indexed Query construction uses the right Source abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L158-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean#L158-L162

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

theorem ThreeSum.BlockIndexedQuery.rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |rightSource P d C c q S| ≤ C.card := by sorry
