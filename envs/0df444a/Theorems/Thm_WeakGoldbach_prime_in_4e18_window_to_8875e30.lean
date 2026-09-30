-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_to_8875e30
-- name    : WeakGoldbach.prime_in_4e18_window_to_8875e30
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T03:46:32.983288+00:00
-- url     : https://prove2.me/theorems/93d33020-bf6e-4029-bd43-1bcb12e18fba
-- title:
--   Prime gaps below $8.875\times 10^{30}$ are smaller than $4\cdot 10^{18}$
-- statement:
--   Put
--
--   $$
--   B = 4\cdot 10^{18}, \qquad T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000.
--   $$
--
--   For every natural number $x \le T - B$ there exists a prime $p$ with
--
--   $$
--   x < p < x + B.
--   $$
--
--   Equivalently, consecutive primes are less than $B$ apart throughout the range below $T$. This is the covering property certified by the Helfgott–Platt computation: their prime ladder places a certified prime rung inside every consecutive window of width $B$, reached interval by interval over the 492,700 blocks of width $2^{54}\cdot 10^{9}$ partitioning $[0, T]$.
--
--   **Formalization Note** The bound $x \le T - B$ suffices for the ladder construction (a rung is only extended while it is below $T - B$).
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, §3–§4: consecutive rungs of the prime ladder are at most Δ = 4·10^18 apart, which is precisely the statement that every window (x, x+Δ) below T contains a prime

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_to_8875e30 (x : ℕ)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
