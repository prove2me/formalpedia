-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
-- name    : ThreeSum.BlockIndex.mem_indexSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:12.306025+00:00
-- url     : https://prove2.me/theorems/3c668c66-88ae-4178-8e84-75e7e446d7b6
-- title:
--   Block Index: mem index Set
-- statement:
--   The Block Index construction uses the mem index Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L35-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L35-L37

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

theorem ThreeSum.BlockIndex.mem_indexSet {J L : ℕ} (S : Finset (Coord J L)) (c : Coord J L) :
    coordEquiv J L c ∈ indexSet S ↔ c ∈ S := by sorry
