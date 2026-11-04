-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le_w3sum_ac885d1
-- name    : ThreeSum.PrimeChain.sum_scores_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:31.947992+00:00
-- url     : https://prove2.me/theorems/45188563-51b6-467d-bb87-bf4446a79adb
-- title:
--   Prime Chain: sum scores le
-- statement:
--   The finite averaging estimate is valid on YES instances too: zero
--   differences are removed by their zero weight.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L63-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L63-L85

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

theorem ThreeSum.PrimeChain.sum_scores_le_w3sum_ac885d1 (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q K : ℕ)
    (hdivisors : ∀ i ∈ T, difference i ≠ 0 →
      (C.filter fun p => p ∣ (difference i).natAbs).card ≤ K) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤ K * score T difference weight q := by sorry
