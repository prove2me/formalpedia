-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_from_4e18_to_8875e30
-- name    : WeakGoldbach.prime_in_4e18_window_from_4e18_to_8875e30
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T03:52:57.337648+00:00
-- url     : https://prove2.me/theorems/95c7efb5-d258-4895-bd06-8fe1d7a39034
-- title:
--   A prime in $(x,\, x+4\cdot 10^{18})$ for $4\cdot 10^{18} \le x \le T - 4\cdot 10^{18}$
-- statement:
--   Put
--
--   $$
--   B = 4\cdot 10^{18}, \qquad T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000.
--   $$
--
--   For every natural number $x$ with
--
--   $$
--   B \le x \le T - B,
--   $$
--
--   there exists a prime $p$ with $x < p < x + B$. This is exactly the portion of the window-covering claim that requires the Helfgott–Platt computation: they certify a ladder rung inside every consecutive window of width $B$ from the binary-verified range up to $T$, over 492,700 intervals of width $2^{54}\cdot 10^{9}$.
--
--   **Formalization Note** Together with the elementary range $x \le B$ (which follows from Bertrand's postulate), this yields the full covering statement `prime_in_4e18_window_to_8875e30`.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, §3–§4 (prime ladder rung gaps at most Δ = 4·10^18 above the verified range)

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_from_4e18_to_8875e30 (x : ℕ)
    (hxl : 4 * 10 ^ 18 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
