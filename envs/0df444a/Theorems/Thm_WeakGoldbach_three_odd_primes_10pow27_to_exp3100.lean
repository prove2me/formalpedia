-- Prove2me | Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
-- name    : WeakGoldbach.three_odd_primes_10pow27_to_exp3100
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T14:50:42.764814+00:00
-- url     : https://prove2.me/theorems/8d56f917-3bf0-4782-bac2-f9435586fa41
-- title:
--   All-odd ternary Goldbach for $10^{27} \le n < e^{3100}$
-- statement:
--   For every odd natural number $n$ with
--
--   $$
--   10^{27} \le n < e^{3100},
--   $$
--
--   there exist **odd** primes $p, q, r$ with $n = p + q + r$.
--
--   This is the effective circle-method regime of the ternary Goldbach theorem: Helfgott's explicit major- and minor-arc bounds on the smoothed prime exponential sum prove a positive representation count for every odd $n$ in this range, and a positive count forces an all-odd triple (the $\{2,2,n-4\}$ representations contribute negligibly).
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748 (effective range)

import Mathlib

namespace WeakGoldbach

theorem three_odd_primes_10pow27_to_exp3100 (n : ℕ)
    (hlo : 10 ^ 27 ≤ n) (hhi : (n : ℝ) < Real.exp 3100) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

end WeakGoldbach
