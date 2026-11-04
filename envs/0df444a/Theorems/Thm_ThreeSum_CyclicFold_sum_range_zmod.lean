-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_sum_range_zmod
-- name    : ThreeSum.CyclicFold.sum_range_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:15.708978+00:00
-- url     : https://prove2.me/theorems/1592768a-cb6d-40f2-b421-f901ac5b31df
-- title:
--   Cyclic Fold: sum range zmod
-- statement:
--   The Cyclic Fold construction uses the sum range zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L77-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L77-L89

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.sum_range_zmod {p : ℕ} [NeZero p] (f : ZMod p → ℤ) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ i : ZMod p, f i := by sorry
