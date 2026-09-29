-- Prove2me | Theorems.Thm_RamareAnalytic_prime_log_moment_tail
-- name    : RamareAnalytic.prime_log_moment_tail
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T20:57:20.797011+00:00
-- url     : https://prove2.me/theorems/ae5c51d4-9e71-4656-94d7-a5a037bac1eb
-- title:
--   An explicit convergent tail bound for the logarithmic prime totient moment
-- statement:
--   For every integer cutoff $X\ge1$, the nonnegative series over primes $p>X$ converges, and
--
--   $$\sum_{\substack{p>X\\p\text{ prime}}}\frac{\log p}{p(p-1)}
--   \le \log4\left(\frac1X+\frac1{X+1}\right).$$
--
--   Here $\log$ denotes the natural logarithm. The series is represented over natural numbers with zero terms at nonprimes and at integers at most $X$. Thus convergence is part of the conclusion, rather than an implicit prerequisite for an infinite-sum expression.
--
--   This quantitative tail controls the constant appearing in harmonic-convolution estimates for squarefree reciprocal totients. It follows from a discrete partial-summation argument and the classical Chebyshev bound $\theta(t)\le(\log4)t$; it is an auxiliary estimate in this formal development, with no optimality or novelty claim.
-- source:
--   Derived auxiliary estimate for O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa22 (1995),645–706, harmonic-convolution constants on printed pp.656–660. https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The exact discrete bound here is derived, not transcribed from that paper. Classical input: Chebyshev.theta_le_log4_mul_x in Mathlib/NumberTheory/Chebyshev.lean, pinned revision0df444a360eaa60ab8c11dca51a86af692955474. Consumer: https://prove2.me/theorems/017351d0-907f-4262-b614-6850111f1ff0 .

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.prime_log_moment_tail (X : ℕ) (hX : 1 ≤ X) :
    Summable (fun p : ℕ =>
      if X < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
    (∑' p : ℕ, if X < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤
      Real.log 4 * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by sorry
