-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_positionalHash_ofFn
-- name    : ThreeSum.BlockIndex.positionalHash_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:19.932356+00:00
-- url     : https://prove2.me/theorems/b28cc4da-3ca4-41da-b481-9acaf09db0f2
-- title:
--   Block Index: positional Hash of Fn
-- statement:
--   The Block Index construction uses the positional Hash of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L77-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L77-L88

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

theorem ThreeSum.BlockIndex.positionalHash_ofFn (p : ℤ) {J : ℕ} (f : Fin J → ℤ) :
    Radix.positionalHash p id (List.ofFn f) = ∑ i : Fin J, p^i.val * f i := by sorry
