-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_4e18_to_1e26
-- name    : WeakGoldbach.prime_in_4e18_window_4e18_to_1e26
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T04:12:27.101993+00:00
-- url     : https://prove2.me/theorems/f83fa300-7479-4e89-ba6c-9bf28ed2bfd5
-- title:
--   A prime in $(x,\,x+4\cdot 10^{18})$ for $4\cdot 10^{18} \le x \le 10^{26}$
-- statement:
--   For every natural number $x$ with
--
--   $$
--   4\cdot 10^{18} \le x \le 10^{26},
--   $$
--
--   there exists a prime $p$ with $x < p < x + 4\cdot 10^{18}$.
--
--   This middle segment of the window-covering claim follows from verified short-interval prime gaps: a prime $p \le y$ with $y - p \le y / (2.8\cdot 10^{7})$ exists for every $y \ge 1.1\cdot 10^{10}$, and applied at $y = x + 4\cdot 10^{18} - 1$ that bound lands inside $(x, x + 4\cdot 10^{18})$ whenever $x \le 10^{26}$.
--
--   **Formalization Note** The corresponding claim is `TaoFivePrimes.prime_in_short_interval`.
-- source:
--   Short-interval prime gap verification used in the five-primes work (Tao); cf. Helfgott–Platt arXiv:1305.3062v2 §4 for the complementary ladder computation

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_4e18_to_1e26 (x : ℕ)
    (hxl : 4 * 10 ^ 18 ≤ x) (hx : x ≤ 10 ^ 26) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
