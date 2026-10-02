-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c4b2
-- name    : TaoFivePrimes.axler_chain_c4b2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T20:17:04.61424+00:00
-- url     : https://prove2.me/theorems/35f9f1d7-880f-486f-b54b-de2c667ccd53
-- title:
--   Chebyshev theta finite certificate: range [42496200, 52597756)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c4b2`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $42496200$:
--   $$42489544241440\le 10^6\theta(42496200)\le 42491283964499$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=52597756$:**
--   $$52589385226535\le 10^6\,\theta(52597756)\le 52591511472754$$
--
--   **Pointwise bound.** For every real $x$ with $42496200\le x<52597756$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[42496200,52597756)$ is partitioned into $320$ consecutive prime-interval blocks grouped into $2$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c4b2 (hprev : (42489544241440 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (42496200 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (42496200 : ℝ) ≤ (42491283964499 : ℝ)) :
    ((52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) ∧
    (∀ x : ℝ, (42496200 : ℝ) ≤ x → x < (52597756 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
