-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c6
-- name    : TaoFivePrimes.axler_chain_c6
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T15:25:19.61023+00:00
-- url     : https://prove2.me/theorems/8497c608-b4c7-4290-9a4f-254a58f061f4
-- title:
--   Chebyshev theta finite certificate: range [87458565, 100000000)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment $k=6$
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $87458565$:
--   $$87444803702622\le 10^6\theta(87458565)\le 87448235987654$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=100000000$:**
--   $$99985797635551\le 10^6\,\theta(100000000)\le 99989691935170$$
--
--   **Pointwise bound.** For every real $x$ with $87458565\le x<100000000$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   As in the first segment, $[87458565,100000000)$ is partitioned into consecutive prime-interval blocks, each block inequality is discharged by kernel computation, and the blocks are chained to give the pointwise bound and the state at the right endpoint.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c6 (hprev : (87444803702622 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ≤ (87448235987654 : ℝ)) :
    ((99985797635551 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (100000000 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (100000000 : ℝ) ≤ (99989691935170 : ℝ)) ∧
    (∀ x : ℝ, (87458565 : ℝ) ≤ x → x < (100000000 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
