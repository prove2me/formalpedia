-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_vector_getD
-- name    : ThreeSum.CyclicFold.vector_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:05.578622+00:00
-- url     : https://prove2.me/theorems/59589685-1db6-4415-b78b-8444ba1b6163
-- title:
--   Cyclic Fold: vector get D
-- statement:
--   The Cyclic Fold construction uses the vector get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L72-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L72-L75

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.vector_getD (p : ℕ) (f : ZMod p → ℕ) (i : ℕ) (hi : i < p) :
    (vector p f).getD i 0 = (f (i : ZMod p) : ℤ) := by sorry
