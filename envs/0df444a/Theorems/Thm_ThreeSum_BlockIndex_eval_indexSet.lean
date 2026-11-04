-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_eval_indexSet
-- name    : ThreeSum.BlockIndex.eval_indexSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:42.994994+00:00
-- url     : https://prove2.me/theorems/075cab60-ed28-4e59-86ae-47b8a6490f1f
-- title:
--   Block Index: eval index Set
-- statement:
--   The Block Index construction uses the eval index Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L63-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L63-L75

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

theorem ThreeSum.BlockIndex.eval_indexSet {J L : ℕ} (S : Finset (Coord J L))
    (w0 w1 : Coord J L → ℕ) :
    OneHotMask.eval (OneHotMask.extend (w0 ∘ (coordEquiv J L).symm))
      (OneHotMask.extend (w1 ∘ (coordEquiv J L).symm))
      (J*L) (SubsetAddress.subsetMask (indexSet S)) =
      ∑ c : Coord J L, if c ∈ S then w1 c else w0 c := by sorry
