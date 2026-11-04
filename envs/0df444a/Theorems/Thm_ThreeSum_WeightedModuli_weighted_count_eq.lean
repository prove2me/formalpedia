-- Prove2me | Theorems.Thm_ThreeSum_WeightedModuli_weighted_count_eq
-- name    : ThreeSum.WeightedModuli.weighted_count_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:02.190961+00:00
-- url     : https://prove2.me/theorems/63a330bf-10bb-4991-a82e-09b774e35bf8
-- title:
--   Weighted Moduli: weighted count eq
-- statement:
--   The Weighted Moduli construction uses the weighted count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L85-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L85-L91

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators

theorem ThreeSum.WeightedModuli.weighted_count_eq {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q =
      C.card * modCount T difference q -
        (∑ p ∈ C, modCount T difference (joint q p)) := by sorry
