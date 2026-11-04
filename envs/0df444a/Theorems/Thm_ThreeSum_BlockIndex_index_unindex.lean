-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_index_unindex
-- name    : ThreeSum.BlockIndex.index_unindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:09.679476+00:00
-- url     : https://prove2.me/theorems/2edf5b0d-884c-43fc-83dd-5a618411c226
-- title:
--   Block Index: index unindex
-- statement:
--   The Block Index construction uses the index unindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L47-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L47-L50

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

theorem ThreeSum.BlockIndex.index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    indexSet (unindexSet (J := J) (L := L) S) = S := by sorry
