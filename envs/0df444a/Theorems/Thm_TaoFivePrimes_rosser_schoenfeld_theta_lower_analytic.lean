-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T09:28:03.800872+00:00
-- url     : https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786
-- title:
--   Rosser–Schoenfeld (1962), Theorem 4, eq. (3.14): analytic lower bound for θ
-- statement:
--   Let $\theta$ be the Chebyshev function, $\theta(t) = \sum_{p \le t} \log p$ over primes $p$. For every real $t \ge 1340$,
--   $$t\left(1 - \frac{1}{2\log t}\right) \;<\; \theta(t).$$
--
--   This is inequality (3.14) of Theorem 4 of Rosser and Schoenfeld (1962), a lower bound for $\theta$ valid in an unbounded range. It is the input used in §9 of that paper (p. 89) to construct the parameter $y$ of Lemma 15 in the range $\log n \ge 1340$: taking $y = 2 + (0.9\log n)/\log\log n$, setting $t = \log n + y$, one has $t \ge 1340$ and $2y\log t \ge 1.8\log n \ge \log n + y = t$, whence $\log n \le t - t/(2\log t) < \theta(t)$.
--
--   Formalization note: `Chebyshev.theta` is Mathlib's $\theta$ function on $\mathbb{R}$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94, Theorem 4, p. 70, eq. (3.14); used in §9, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic (t : ℝ) (h1 : 1340 ≤ t) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry

end TaoFivePrimes
