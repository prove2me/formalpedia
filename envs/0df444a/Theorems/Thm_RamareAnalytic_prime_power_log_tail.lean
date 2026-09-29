-- Prove2me | Theorems.Thm_RamareAnalytic_prime_power_log_tail
-- name    : RamareAnalytic.prime_power_log_tail
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T21:24:50.840611+00:00
-- url     : https://prove2.me/theorems/48d578fb-8635-4c36-acb7-5cfc4e8fafcc
-- title:
--   Chebyshev bound for prime logarithms with power-decaying weights
-- statement:
--   For every integer $m\ge1$ and real exponent $s>1$, the prime tail converges unconditionally and obeys
--
--   $$\sum_{p\ge m,\;p\text{ prime}}\frac{\log p}{p^s}\le\log(4)\frac{s}{s-1}m^{1-s}.$$
--
--   The formal statement enumerates all integers at least $m$ by $m+k$ and uses a prime indicator. The proof uses the actual Chebyshev bound $\theta(x)\le x\log4$, a finite summation-by-parts comparison, and the integral of $x^{-s}$. It derives convergence from bounded nonnegative partial sums, so neither convergence nor a tail estimate is an assumption.
--
--   The two specializations $s=8/5$ and $s=6/5$ control the tail of the weighted Euler product in the Ramaré squarefree reciprocal-totient argument. This result supplies those analytic tails; the finite Euler factors and the final numerical product bound are separate results.
-- source:
--   Chebyshev theta bound and the classical summation-by-parts/integral-comparison argument. The pinned primary formal source is Mathlib.NumberTheory.Chebyshev, theorem Chebyshev.theta_le_log4_mul_x, at revision0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean . Intended application: O. Ramaré, On Shnirelman's constant, Section3, https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The exponents2/5,8/5,6/5 are auxiliary choices of this formal development.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.prime_power_log_tail (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by sorry
