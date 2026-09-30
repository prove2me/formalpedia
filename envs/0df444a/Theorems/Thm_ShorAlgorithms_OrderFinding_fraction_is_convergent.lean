-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_fraction_is_convergent
-- name    : ShorAlgorithms.OrderFinding.fraction_is_convergent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T09:29:26.182534+00:00
-- url     : https://prove2.me/theorems/2377e57b-44a5-47ed-8474-d004fedf61af
-- title:
--   §5, p. 1500 — the fraction near $c/q$ is a continued-fraction convergent of $c/q$
-- statement:
--   Let $n, q, c$ be natural numbers with $n^2 \le q$, and let $s$ be a rational number whose denominator in lowest terms is smaller than $n$ and which satisfies
--
--   $$
--   \left|\frac{c}{q} - s\right| \le \frac{1}{2q}.
--   $$
--
--   Then $s$ is one of the convergents of the continued fraction expansion of the real number $c/q$.
--
--   This is why the continued fraction expansion of $c/q$ finds the fraction $d/r$ that the rounding step of the algorithm needs.
--
--   **Formalization Note** Convergents are Mathlib's `Real.convergent`. The polynomial running time of the continued fraction algorithm, also mentioned in the paper's sentence, is not stated.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1500, §5, "This fraction can be found in polynomial time by using a continued fraction expansion of c/q, which finds all the best approximations of c/q by fractions"

import Mathlib

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, p. 1500: the fraction found by rounding is among the continued-fraction
convergents of `c/q`. If `n² ≤ q` and a rational `s` with lowest-terms denominator smaller
than `n` satisfies `|c/q - s| ≤ 1/(2q)`, then `s` is a convergent of the continued fraction
expansion of `c/q`. -/
theorem fraction_is_convergent (n q c : ℕ) (hnq : n ^ 2 ≤ q) (s : ℚ) (hs : s.den < n)
    (h : |(c : ℝ) / q - (s : ℝ)| ≤ 1 / (2 * q)) :
    ∃ m : ℕ, s = ((c : ℝ) / q).convergent m := by sorry

end ShorAlgorithms.OrderFinding
