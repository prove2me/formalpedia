-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_sum_scores
-- name    : ThreeSum.PrimeChain.sum_scores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:29.478396+00:00
-- url     : https://prove2.me/theorems/b9ff92d3-a0d5-4072-969b-69b407ab6dcf
-- title:
--   Prime Chain: sum scores
-- statement:
--   The Prime Chain construction uses the sum scores property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L49-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L49-L59

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}

theorem ThreeSum.PrimeChain.sum_scores (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (C : Finset ℕ) (q : ℕ) :
    (∑ p ∈ C, score T difference weight (q * p)) =
      ∑ i ∈ T, (C.filter fun p => q * p ∣ (difference i).natAbs).card *
        weight (difference i) := by sorry
