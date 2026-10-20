-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_window_of_ladder_strict
-- name    : WeakGoldbach.prime_in_window_of_ladder_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T17:42:20.195772+00:00
-- url     : https://prove2.me/theorems/e1ba8433-932d-4261-a1d5-f131c35fd308
-- title:
--   A prime ladder with a top rung strictly past $T-B$ covers every window $(x, x+B)$
-- statement:
--   Let $B = 4\cdot 10^{18}$ and $T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000$, and let $p_0 < p_1 < \dots < p_k$ be odd primes with
--
--   $$p_0 \le B, \qquad p_i < p_{i+1} < p_i + B, \qquad T < p_k + B .$$
--
--   Then for every $x \le T - B$ the open window $(x, x+B)$ contains a prime:
--
--   $$\exists q,\quad x < q < x + B,\quad q \text{ prime.}$$
--
--   **The argument.** Take the largest ladder index $j$ with $p_j \le x$. It exists because $p_0 \le x$ once $x \ge p_0$, and the small cases $x < 2$ and $x < p_0$ are handled directly. If $j = k$ then $p_k \le x \le T - B$ together with $T < p_k + B$ gives $p_k > T - B \ge x$, a contradiction; so $j < k$, and then $p_{j+1} > x$ by maximality while $p_{j+1} < p_j + B \le x + B$ by the gap bound. Hence $p_{j+1}$ is the wanted prime.
--
--   **Why the strict inequality at the top matters.** With $T \le p_k + B$ instead of $T < p_k + B$, the single value $x = T - B$ escapes: then $p_k$ may equal $T - B$ exactly, and the ladder supplies no rung above it, so the interval $(x, x+B)$ is not covered by the argument. The strict form removes that case and is what the window claims need.
--
--   **Formalization Note.** Pure interval arithmetic on $\mathbb{N}$; the ladder's parity is irrelevant and not assumed.
-- source:
--   Helfgott-Platt prime ladder (arxiv 1305.3062), as isolated on this platform in WeakGoldbach.prime_ladder_to_8875e30; the strict-top variant is what WeakGoldbach.prime_in_4e18_window_to_8875e30 requires.

import Mathlib

namespace WeakGoldbach

theorem prime_in_window_of_ladder_strict (k : ℕ) (p : ℕ → ℕ)
    (hprime : ∀ i, i ≤ k → Nat.Prime (p i))
    (h0 : p 0 ≤ 4 * 10 ^ 18)
    (hstep : ∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18)
    (htop : 8875694145621773516800000000000 < p k + 4 * 10 ^ 18)
    (x : ℕ) (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ q : ℕ, x < q ∧ q < x + 4 * 10 ^ 18 ∧ Nat.Prime q := by sorry

end WeakGoldbach
