-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c5c
-- name    : TaoFivePrimes.axler_chain_c5c
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T18:32:31.139819+00:00
-- url     : https://prove2.me/theorems/0ff90fcd-9110-42c8-b6b6-9cb63c3342cc
-- title:
--   Chebyshev theta finite certificate: range [77727216, 87458565)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c5c`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $77727216$:
--   $$77716973602484\le 10^6\theta(77727216)\le 77720044899979$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=87458565$:**
--   $$87444803702622\le 10^6\,\theta(87458565)\le 87448235987654$$
--
--   **Pointwise bound.** For every real $x$ with $77727216\le x<87458565$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[77727216,87458565)$ is partitioned into $177$ consecutive prime-interval blocks grouped into $2$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c5c (hprev : (77716973602484 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (77727216 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (77727216 : ℝ) ≤ (77720044899979 : ℝ)) :
    ((87444803702622 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ≤ (87448235987654 : ℝ)) ∧
    (∀ x : ℝ, (77727216 : ℝ) ≤ x → x < (87458565 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
