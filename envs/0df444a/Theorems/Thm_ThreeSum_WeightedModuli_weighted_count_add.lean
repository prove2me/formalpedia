-- Prove2me | Theorems.Thm_ThreeSum_WeightedModuli_weighted_count_add
-- name    : ThreeSum.WeightedModuli.weighted_count_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:01.251628+00:00
-- url     : https://prove2.me/theorems/fbf6caac-85c6-4373-bccd-391e780faaa3
-- title:
--   Weighted Moduli: weighted count add
-- statement:
--   The Weighted Moduli construction uses the weighted count add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L68-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L68-L83

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators

theorem ThreeSum.WeightedModuli.weighted_count_add {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q +
      (∑ p ∈ C, modCount T difference (joint q p)) =
      C.card * modCount T difference q := by sorry
