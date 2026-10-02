-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c5
-- name    : TaoFivePrimes.axler_chain_c5
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-01T15:25:19.690419+00:00
-- url     : https://prove2.me/theorems/2b1358f4-3525-431c-ac07-eacdd6d3f73a
-- title:
--   Chebyshev theta finite certificate: range [52597756, 87458565)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment $k=5$
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $52597756$:
--   $$52589385226535\le 10^6\theta(52597756)\le 52591511472754$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=87458565$:**
--   $$87444803702622\le 10^6\,\theta(87458565)\le 87448235987654$$
--
--   **Pointwise bound.** For every real $x$ with $52597756\le x<87458565$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   As in the first segment, $[52597756,87458565)$ is partitioned into consecutive prime-interval blocks, each block inequality is discharged by kernel computation, and the blocks are chained to give the pointwise bound and the state at the right endpoint.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c5 (hprev : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) :
    ((87444803702622 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ≤ (87448235987654 : ℝ)) ∧
    (∀ x : ℝ, (52597756 : ℝ) ≤ x → x < (87458565 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
