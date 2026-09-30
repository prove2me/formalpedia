-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_window_4e18_add_two
-- name    : WeakGoldbach.prime_in_window_4e18_add_two
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T02:57:55.9415+00:00
-- url     : https://prove2.me/theorems/9e3719c6-75e9-4525-a316-a538f4c9a747
-- title:
--   Prime ladder step: a prime in $[n-4\cdot 10^{18}-2,\, n-4]$ for each odd $n \le 8.875\times 10^{30}$
-- statement:
--   This is the covering property certified by the Helfgott–Platt prime ladder computation.
--
--   For every odd natural number $n$ with
--
--   $$
--   4\cdot 10^{18} + 5 \le n \le 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000 =: T,
--   $$
--
--   there exists a prime $p$ with
--
--   $$
--   4 \le n - p \le 4\cdot 10^{18} + 2,
--   $$
--
--   i.e. the interval $[n - 4\cdot 10^{18} - 2,\, n - 4]$ contains a prime.
--
--   Helfgott and Platt computed an explicit ladder of primes $r_0 < r_1 < \dots$ reaching past $T$, each consecutive rung at most $\Delta = 4\cdot 10^{18}$ apart (rungs are Proth primes $k\cdot 2^{52} + 1$ where available, certified by Proth's theorem, and general primes otherwise). Taking $p$ to be the largest rung at most $n - 4$, the next rung satisfies $r_{j+1} \ge n - 2$ (since $n - 3$ is even and exceeds $2$), whence
--
--   $$
--   n - p = (n - r_{j+1}) + (r_{j+1} - r_j) \le 2 + \Delta.
--   $$
--
--   **Formalization Note** The distance is stated on `Nat` truncated subtraction; since $4 \le n - p$ it agrees with the integer difference.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, §3 (the prime ladder algorithm, rung gap Δ = 4·10^18) and §4 (implementation over 492,700 intervals of width 2^54·10^9 reaching T), https://arxiv.org/abs/1305.3062

import Mathlib

namespace WeakGoldbach

theorem prime_in_window_4e18_add_two (n : ℕ) (hodd : Odd n)
    (hlo : 4 * 10 ^ 18 + 5 ≤ n) (hhi : n ≤ 8875694145621773516800000000000) :
    ∃ p : ℕ, Nat.Prime p ∧ 4 ≤ n - p ∧ n - p ≤ 4 * 10 ^ 18 + 2 := by
  sorry

end WeakGoldbach
