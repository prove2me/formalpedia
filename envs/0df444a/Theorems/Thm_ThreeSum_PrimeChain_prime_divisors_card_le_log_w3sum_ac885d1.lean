-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_prime_divisors_card_le_log_w3sum_ac885d1
-- name    : ThreeSum.PrimeChain.prime_divisors_card_le_log_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:27.667196+00:00
-- url     : https://prove2.me/theorems/bd9ba147-3c79-4d3f-8cc1-940940ab648b
-- title:
--   Prime Chain: prime divisors card le log
-- statement:
--   A nonzero integer cannot have too many distinct prime divisors above y.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L29-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L29-L47

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

theorem ThreeSum.PrimeChain.prime_divisors_card_le_log_w3sum_ac885d1 (C : Finset ℕ) (y : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (z : ℤ) (hz : z ≠ 0) :
    (C.filter fun p => p ∣ z.natAbs).card ≤ Nat.log y z.natAbs := by sorry
