-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_indexSet_injective
-- name    : ThreeSum.BlockIndex.indexSet_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:57.935792+00:00
-- url     : https://prove2.me/theorems/2c8ddf6b-8ad9-4e0b-b446-8580d7106dbe
-- title:
--   Block Index: index Set injective
-- statement:
--   The Block Index construction uses the index Set injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L52-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L52-L53

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

theorem ThreeSum.BlockIndex.indexSet_injective (J L : ℕ) : Function.Injective (@indexSet J L) := by sorry
