-- Prove2me | Theorems.Thm_QuantumLTF_Membership_ceil_logb_bits_bound
-- name    : QuantumLTF.Membership.ceil_logb_bits_bound
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T04:32:20.484489+00:00
-- url     : https://prove2.me/theorems/b41992c1-6686-4146-a8d8-4f946c478ef3
-- title:
--   Base-two ceiling gives a logarithmic bit bound
-- statement:
--   There is a universal positive constant bounding four plus the natural ceiling of the base-two logarithm of n by that constant times the natural logarithm of n, for every n at least two.
-- source:
--   Bit-complexity estimate used in Lemma 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib

theorem QuantumLTF.Membership.ceil_logb_bits_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ((4 + ⌈Real.logb 2 n⌉₊ : ℕ) : ℝ) ≤ C * Real.log n := by sorry
