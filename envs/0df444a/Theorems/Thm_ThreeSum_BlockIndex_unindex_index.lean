-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_unindex_index
-- name    : ThreeSum.BlockIndex.unindex_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:12.723566+00:00
-- url     : https://prove2.me/theorems/bf5f2373-6280-47c5-8720-8284c8edbfda
-- title:
--   Block Index: unindex index
-- statement:
--   The Block Index construction uses the unindex index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L42-L45

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_BlockIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndex
open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.BlockIndex.unindex_index {J L : ℕ} (S : Finset (Coord J L)) :
    unindexSet (indexSet S) = S := by sorry
