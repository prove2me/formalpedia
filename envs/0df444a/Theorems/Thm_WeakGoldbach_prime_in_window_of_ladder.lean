-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_window_of_ladder
-- name    : WeakGoldbach.prime_in_window_of_ladder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T15:50:17.063656+00:00
-- url     : https://prove2.me/theorems/0b856e8b-832a-4f70-927a-a5f0d4fe2ff7
-- title:
--   A prime ladder with gaps below $4\cdot10^{18}$ gives prime coverage of every window $[n-B-2,\,n-4]$
-- statement:
--   Let $B = 4\cdot 10^{18}$ and $T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000$. Suppose $p_0 < p_1 < \dots < p_k$ is a finite sequence of odd primes with
--
--   $$p_0 \le B, \qquad p_i < p_{i+1} < p_i + B \ \ (0 \le i < k), \qquad T \le p_k + B .$$
--
--   Then for every natural number $n$ with $B + 5 \le n \le T$ there is a prime $q$ with
--
--   $$4 \;\le\; n - q \;\le\; B + 2 ,$$
--
--   that is, the window $[n - B - 2,\ n - 4]$ contains a prime.
--
--   **What this is.** It is the pure pigeonhole step that converts a prime ladder into window coverage, and it is the elementary half of the Helfgott–Platt covering computation: the ladder is the hard arithmetic input (a verified list of primes reaching $8.9\cdot10^{30}$ with consecutive gaps below $4\cdot10^{18}$), while the passage from a ladder to "every $n$ in the range has a prime inside $[n - B - 2, n-4]$" involves no number theory at all.
--
--   **The argument.** Take the largest ladder index $j$ with $p_j \le n - 4$; it exists because $p_0 \le B < n - 4$. If $p_j < n - B - 2$, then either $j = k$, in which case $p_k + B < n - 2 < n \le T \le p_k + B$, a contradiction; or $j < k$, in which case maximality of $j$ forces $p_{j+1} \ge n - 3$ while the gap bound gives $p_{j+1} < p_j + B \le n - 3$, also a contradiction. Hence $p_j \in [n - B - 2, n - 4]$, and $q = p_j$ is the required prime.
--
--   **Formalization Note.** The bound $B + 5 \le n$ in the statement is what makes both truncated subtractions genuine; the parity hypothesis `Odd n` is part of the interface taken from the target statement and is not needed by the argument.
-- source:
--   Helfgott-PLatt prime ladder, as isolated on this platform in WeakGoldbach.prime_ladder_to_8875e30 and consumed by WeakGoldbach.prime_in_window_4e18_add_two; the argument is the pigeonhole step between them and appears in the Helfgott-Platt bounded ternary Goldbach verification, https://arxiv.org/abs/1305.3062, section on the ladder construction.

import Mathlib

namespace WeakGoldbach

theorem prime_in_window_of_ladder (k : ℕ) (p : ℕ → ℕ) (n : ℕ)
    (hprime : ∀ i, i ≤ k → Nat.Prime (p i) ∧ Odd (p i))
    (h0 : p 0 ≤ 4 * 10 ^ 18)
    (hstep : ∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18)
    (htop : 8875694145621773516800000000000 ≤ p k + 4 * 10 ^ 18)
    (hodd : Odd n)
    (hlo : 4 * 10 ^ 18 + 5 ≤ n)
    (hhi : n ≤ 8875694145621773516800000000000) :
    ∃ q : ℕ, Nat.Prime q ∧ 4 ≤ n - q ∧ n - q ≤ 4 * 10 ^ 18 + 2 := by sorry

end WeakGoldbach
