-- Prove2me | Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27
-- name    : WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : Open
-- author  : @miao
-- created : 2026-09-10T12:33:38.978158+00:00
-- url     : https://prove2.me/theorems/03a3f003-9a68-4b79-866e-245c16acd539
-- title:
--   Helfgott’s analytic range: three odd primes for $n \ge 10^{27}$
-- statement:
--   This is the explicit large-number range in Helfgott’s analytic proof of the ternary Goldbach conjecture.
--
--   Let $n$ be an odd natural number with $n \ge 10^{27}$. Then there exist odd primes $p_1,p_2,p_3$ such that
--
--   $$
--   n=p_1+p_2+p_3.
--   $$
--
--   The statement isolates the analytic half of the final argument, independently of the bounded computational verification.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, §7.4, pp. 69–71; conclusion on p. 70, https://arxiv.org/abs/1312.7748

import Mathlib

namespace WeakGoldbach

theorem three_odd_primes_ge_10pow27 (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by sorry

end WeakGoldbach
