-- Prove2me | Theorems.Thm_Plasticity_Ext_KMRate_binomial_sum_le
-- name    : Plasticity.Ext.KMRate.binomial_sum_le
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T17:55:18.102564+00:00
-- url     : https://prove2.me/theorems/fd0e1b73-9736-4827-a61b-050f172fd1a1
-- title:
--   A binomial average of ballot probabilities is at most √(2/(π n u))
-- statement:
--   For every $n\ge0$ and $0\le u\le\tfrac12$,
--   $$\sqrt{nu}\,\sum_{m=0}^{n}\binom nm u^m(1-u)^{n-m}\,\frac{\binom{m}{\lfloor m/2\rfloor}}{2^m}\le\sqrt{\frac2\pi}.$$
--   The constant is sharp: for fixed $u\in(0,\tfrac12)$ the left side increases to $\sqrt{2/\pi}$ as $n\to\infty$.
-- source:
--   R. Cominetti, J. A. Soto and J. Vaisman, Israel J. Math. 199 (2014), 757–772 (arXiv:1206.4195), Proposition 8 (stated there for 0 < u < 1/2; u = 0 is trivial and u = 1/2 follows by continuity)

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic

namespace Plasticity.Ext.KMRate
theorem binomial_sum_le (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.sqrt (n * u) * ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * u ^ m * (1 - u) ^ (n - m) * ((m.choose (m / 2) : ℝ) / 2 ^ m)
      ≤ Real.sqrt (2 / Real.pi) := by sorry
end Plasticity.Ext.KMRate
