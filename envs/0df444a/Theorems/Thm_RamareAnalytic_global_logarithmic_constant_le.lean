-- Prove2me | Theorems.Thm_RamareAnalytic_global_logarithmic_constant_le
-- name    : RamareAnalytic.global_logarithmic_constant_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T21:20:25.737897+00:00
-- url     : https://prove2.me/theorems/dea0c4a9-4c03-4233-b6e4-200eae87fc04
-- title:
--   Certified upper bound for the Ramaré logarithmic constant
-- statement:
--   The prime logarithmic series converges unconditionally, and its sum together with the Euler–Mascheroni constant satisfies
--
--   $$\gamma+\sum_{p\text{ prime}}\frac{\log p}{p(p-1)}\le\frac{67}{50}=1.34.$$
--
--   No analytic or numerical certificate is a premise. The proof bounds the actual finite prime sum up to 1000 by 943/1250, bounds gamma by 233/400 using a harmonic sum and a certified logarithm, and controls all primes above 1000 through a Chebyshev–Abel tail estimate. The finite prime set is covered by an exact certificate; individual logarithms use rational upper bounds. Infinite-series convergence is part of the conclusion.
--
--   This is a deliberately conservative bound for the center of the Ramaré squarefree reciprocal-totient asymptotic. The separate bound on the weighted correction moment is still needed for the final finite-N inequality. The formal sum is indexed by all natural numbers with a prime indicator; nonprime indices, including zero and one, contribute zero.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, harmonic-convolution constants in Section 3, printed pp. 656–660. https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The endpoint67/50 and rational certificates are auxiliary choices of this formal development. The quantitative prime tail is https://prove2.me/theorems/ae5c51d4-9e71-4656-94d7-a5a037bac1eb ; the harmonic-convolution consumer is https://prove2.me/theorems/c5e5cedf-d538-4888-b726-db041653e0b7 .

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.global_logarithmic_constant_le :
    Summable (fun p : ℕ =>
      if p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
      Real.eulerMascheroniConstant +
        (∑' p : ℕ, if p.Prime then
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤ (67 : ℝ) / 50 := by sorry
