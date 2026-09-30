-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_fraction_unique
-- name    : ShorAlgorithms.OrderFinding.fraction_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T09:24:16.454687+00:00
-- url     : https://prove2.me/theorems/a2a546c9-1b5e-4efd-9e5d-b72a145fb370
-- title:
--   §5, eq. (5.13) — at most one fraction with denominator $< n$ within $1/2q$ of $c/q$
-- statement:
--   Let $n, q, c$ be natural numbers with $n^2 \le q$. If $s_1$ and $s_2$ are rational numbers whose denominators in lowest terms are smaller than $n$ and which both satisfy
--
--   $$
--   \left|\frac{c}{q} - s_i\right| \le \frac{1}{2q}, \qquad i = 1, 2,
--   $$
--
--   then $s_1 = s_2$.
--
--   So the fraction $d/r$ singled out by (5.13) is determined by $c$ and $q$ alone, which is what makes rounding $c/q$ a well-defined way to recover it.
--
--   **Formalization Note** The paper writes "Because $q > n^2$", but its choice of $q$ on p. 1498 only guarantees $n^2 \le q$ (with equality when $n$ is a power of $2$). The statement holds under $n^2 \le q$, which is the hypothesis used here; this is the stronger theorem. The value $c$ is not required to be smaller than $q$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1500, §5, eq. (5.13) and "Because q > n^2, there is at most one fraction d/r with r < n that satisfies the above inequality"

import Mathlib

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, eq. (5.13), p. 1500: if `n² ≤ q`, there is at most one fraction with
(lowest-terms) denominator smaller than `n` within `1/(2q)` of `c/q`. The page writes
"Because `q > n²`"; the choice of `q` on p. 1498 only gives `n² ≤ q`, and the claim holds
under that weaker hypothesis, which is what is stated here. -/
theorem fraction_unique (n q c : ℕ) (hnq : n ^ 2 ≤ q) (s₁ s₂ : ℚ)
    (h₁ : s₁.den < n) (h₂ : s₂.den < n)
    (hs₁ : |(c : ℚ) / q - s₁| ≤ 1 / (2 * q)) (hs₂ : |(c : ℚ) / q - s₂| ≤ 1 / (2 * q)) :
    s₁ = s₂ := by sorry

end ShorAlgorithms.OrderFinding
