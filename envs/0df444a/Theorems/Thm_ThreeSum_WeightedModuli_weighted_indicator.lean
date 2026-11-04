-- Prove2me | Theorems.Thm_ThreeSum_WeightedModuli_weighted_indicator
-- name    : ThreeSum.WeightedModuli.weighted_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:03.546333+00:00
-- url     : https://prove2.me/theorems/9d0b125d-8130-4e4c-8723-3facad701a68
-- title:
--   Weighted Moduli: weighted indicator
-- statement:
--   The Weighted Moduli construction uses the weighted indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L42-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L42-L66

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators

theorem ThreeSum.WeightedModuli.weighted_indicator (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (q : ℕ) (z : ℤ) :
    (if (q : ℤ) ∣ z then missWeight (Auxiliary.moduli C) z else 0) +
      (∑ p ∈ C, dividesIndicator (joint q p) z) =
      C.card * dividesIndicator q z := by sorry
