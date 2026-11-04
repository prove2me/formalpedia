-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le_log
-- name    : ThreeSum.PrimeChain.sum_scores_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:36.938748+00:00
-- url     : https://prove2.me/theorems/d08ee85f-2ac4-48fd-897f-d2bf697957a1
-- title:
--   Prime Chain: sum scores le log
-- statement:
--   The Prime Chain construction uses the sum scores le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L87-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L87-L96

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

theorem ThreeSum.PrimeChain.sum_scores_le_log (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q y M : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (hbound : ∀ i ∈ T, (difference i).natAbs ≤ M) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤
      Nat.log y M * score T difference weight q := by sorry
