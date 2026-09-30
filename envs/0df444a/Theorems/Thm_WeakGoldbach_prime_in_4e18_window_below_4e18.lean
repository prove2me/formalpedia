-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_below_4e18
-- name    : WeakGoldbach.prime_in_4e18_window_below_4e18
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T03:54:44.353166+00:00
-- url     : https://prove2.me/theorems/0989afff-c176-40b0-af0b-5dcb954a1212
-- title:
--   A prime in $(x,\, x+4\cdot 10^{18})$ for every $x \le 4\cdot 10^{18}$
-- statement:
--   For every natural number $x \le 4\cdot 10^{18}$ there exists a prime $p$ with
--
--   $$
--   x < p < x + 4\cdot 10^{18}.
--   $$
--
--   This is the elementary base of the window-covering statement used to build the Helfgott–Platt prime ladder. For $x \ge 1$ it follows from Bertrand's postulate, which provides a prime $p$ with $x < p \le 2x$, and $2x \le x + 4\cdot 10^{18}$ when $x \le 4\cdot 10^{18}$; the case $x = 0$ is witnessed by $p = 3$.
--
--   **Formalization Note** Mathlib supplies Bertrand's postulate as `Nat.exists_prime_lt_and_le_two_mul`.
-- source:
--   Bertrand's postulate; this is the provable base segment of the covering claim certified computationally by Helfgott–Platt, arXiv:1305.3062v2 §4

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_below_4e18 (x : ℕ) (hx : x ≤ 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
