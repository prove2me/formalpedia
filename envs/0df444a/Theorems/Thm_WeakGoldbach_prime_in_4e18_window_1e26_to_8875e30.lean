-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_1e26_to_8875e30
-- name    : WeakGoldbach.prime_in_4e18_window_1e26_to_8875e30
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T04:12:43.503687+00:00
-- url     : https://prove2.me/theorems/1fdea836-652e-4bd4-8ef2-b15692ceba7b
-- title:
--   A prime in $(x,\,x+4\cdot 10^{18})$ for $10^{26} \le x \le T - 4\cdot 10^{18}$
-- statement:
--   Put
--
--   $$
--   B = 4\cdot 10^{18}, \qquad T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000.
--   $$
--
--   For every natural number $x$ with $10^{26} \le x \le T - B$ there exists a prime $p$ with $x < p < x + B$.
--
--   This is the segment of the window-covering claim beyond the reach of the $x/(2.8\cdot 10^{7})$ short-interval bound, so it is the part that specifically requires the Helfgott–Platt prime-ladder computation up to $T$.
--
--   **Formalization Note** Combined with the elementary segment $x \le B$ (Bertrand) and the middle segment $B \le x \le 10^{26}$ (short-interval gaps), this completes the cover of $x \le T - B$.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, §4

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_1e26_to_8875e30 (x : ℕ)
    (hxl : 10 ^ 26 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
