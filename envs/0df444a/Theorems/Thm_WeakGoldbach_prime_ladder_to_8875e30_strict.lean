-- Prove2me | Theorems.Thm_WeakGoldbach_prime_ladder_to_8875e30_strict
-- name    : WeakGoldbach.prime_ladder_to_8875e30_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T17:42:18.534994+00:00
-- url     : https://prove2.me/theorems/4fff017e-c92b-4832-84b8-62d897f71f24
-- title:
--   Prime ladder to $8.9\cdot10^{30}$ with a top rung strictly past $T-B$
-- statement:
--   Put $B = 4\cdot10^{18}$ and $T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000$. There is a finite increasing sequence of primes $p_0, \dots, p_k$ with
--
--   $$p_0 \le B, \qquad p_i < p_{i+1} < p_i + B \ \ (0 \le i < k), \qquad T < p_k + B .$$
--
--   This is the covering certificate underlying the bounded ternary Goldbach verification of Helfgott and Platt, in the form the window claims need: consecutive rungs closer than $B$, starting below $B$, and the last rung *strictly* far enough that $T - B < p_k$.
--
--   **Relation to the existing node.** The platform node `WeakGoldbach.prime_ladder_to_8875e30` states the same thing with $T \le p_k + B$ and additionally requires the rungs to be odd. The strict inequality here is stronger by one case, and that case is exactly the value $x = T - B$ in the window statements `WeakGoldbach.prime_in_4e18_window_*`: if the top rung sits exactly at $T - B$, the ladder gives no prime above it and the window argument does not close. A certificate with the top rung strictly beyond $T - B$ is what makes the windows follow.
--
--   **Formalization Note.** Primality, ordering, spacing and the endpoint inequality only; no analytic input.
-- source:
--   Helfgott-Platt prime ladder, arxiv 1305.3062 (bounded ternary Goldbach); strict-top variant of the platform node WeakGoldbach.prime_ladder_to_8875e30.

import Mathlib

namespace WeakGoldbach

theorem prime_ladder_to_8875e30_strict :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      p 0 ≤ 4 * 10 ^ 18 ∧
      (∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18) ∧
      8875694145621773516800000000000 < p k + 4 * 10 ^ 18 := by sorry

end WeakGoldbach
