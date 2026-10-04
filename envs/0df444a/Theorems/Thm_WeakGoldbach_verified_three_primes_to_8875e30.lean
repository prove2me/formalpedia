-- Prove2me | Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
-- name    : WeakGoldbach.verified_three_primes_to_8875e30
-- status  : Open
-- author  : @miao
-- created : 2026-09-10T12:33:39.892867+00:00
-- url     : https://prove2.me/theorems/9e5527d9-b474-46f5-b53a-d8bc045c7663
-- title:
--   Verified ternary Goldbach range through $8.875\times10^{30}$
-- statement:
--   This is Helfgott and Platt’s numerical verification of the ternary Goldbach conjecture.
--
--   Let $n$ be an odd natural number satisfying
--
--   $$
--   7 \le n \le 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000.
--   $$
--
--   Then there exist primes $p_1,p_2,p_3$ such that
--
--   $$
--   n=p_1+p_2+p_3.
--   $$
--
--   The theorem supplies the bounded computational half of Helfgott’s final argument and can be reused in other explicit Goldbach reductions.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, Theorem 4.1, p. 3, https://arxiv.org/abs/1305.3062

import Mathlib

namespace WeakGoldbach

theorem verified_three_primes_to_8875e30
    (n : ℕ) (hlo : 7 ≤ n)
    (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by sorry

end WeakGoldbach
