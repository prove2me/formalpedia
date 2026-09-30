-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_outcome_prob_ge
-- name    : ShorAlgorithms.OrderFinding.outcome_prob_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:19:07.667911+00:00
-- url     : https://prove2.me/theorems/7175e6df-8cce-449d-b24c-02eb43f5b6b8
-- title:
--   §5, eq. (5.11) — each state $|c, x^k\rangle$ with $|\{rc\}_q| \le r/2$ has probability $\ge 1/3r^2$
-- statement:
--   There is a threshold $N$ such that the following holds for every $n \ge N$. Let $x$ be coprime to $n$ with multiplicative order $r$ modulo $n$, let $q = 2^l$ satisfy $n^2 \le q < 2n^2$, let $0 \le c < q$ and $0 \le k < r$, and suppose there is an integer $d$ with
--
--   $$
--   -\frac{r}{2} \le rc - dq \le \frac{r}{2}.
--   $$
--
--   Then the probability of observing $|c, x^k \bmod n\rangle$ in the final state (5.4) is at least
--
--   $$
--   \frac{1}{3r^2}.
--   $$
--
--   The hypothesis is the paper's condition (5.12), equivalently (5.11), $-r/2 \le \{rc\}_q \le r/2$, where $\{rc\}_q$ is the residue of $rc$ modulo $q$ in $(-q/2, q/2]$. This per-state bound is what the count of good outcomes turns into the success probability $\varphi(r)/3r$.
--
--   **Formalization Note** The threshold $N$ is quantified before $n$, $x$, $q$, $c$ and $k$, so it is uniform in all of them, as in the paper's "for sufficiently large $n$". The condition is stated in the form (5.12) with an integer $d$, which avoids defining the symmetric residue; the two forms are equivalent because $r/2 < q/2$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1500, §5, eqs. (5.11)–(5.12) and "so is at least 1/3r^2 for sufficiently large n"

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, eqs. (5.11)–(5.12), p. 1500. For all sufficiently large `n` (the threshold
`N` is uniform in `x`, `q`, `c`, `k`): if `x` is coprime to `n` with order `r`, `q = 2^l` with
`n² ≤ q < 2n²`, `0 ≤ k < r`, and there is an integer `d` with `-r/2 ≤ rc - dq ≤ r/2`
(equivalently `-r/2 ≤ {rc}_q ≤ r/2`), then the probability of observing `|c, x^k (mod n)⟩`
is at least `1/(3r²)`. -/
theorem outcome_prob_ge : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℕ, Nat.Coprime x n →
    ∀ q l : ℕ, q = 2 ^ l → n ^ 2 ≤ q → q < 2 * n ^ 2 →
    ∀ c : Fin q, ∀ k : ℕ, k < orderOf (x : ZMod n) →
    (∃ d : ℤ,
        -((orderOf (x : ZMod n) : ℝ) / 2) ≤
          (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ∧
        (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ≤
          (orderOf (x : ZMod n) : ℝ) / 2) →
    1 / (3 * (orderOf (x : ZMod n) : ℝ) ^ 2) ≤ outcomeProb n x q c ((x : ZMod n) ^ k) := by sorry

end ShorAlgorithms.OrderFinding
