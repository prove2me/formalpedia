-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
-- name    : ThreeSum.BlockIndex.indexSet_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:26.223559+00:00
-- url     : https://prove2.me/theorems/929d1f4c-2c50-4203-9f97-d141cdabadea
-- title:
--   Block Index: index Set union
-- statement:
--   The Block Index construction uses the index Set union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L59-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L59-L61

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

theorem ThreeSum.BlockIndex.indexSet_union {J L : ℕ} (S T : Finset (Coord J L)) :
    indexSet (S∪T) = indexSet S ∪ indexSet T := by sorry
