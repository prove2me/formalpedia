-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c5a
-- name    : TaoFivePrimes.axler_chain_c5a
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T18:32:27.732925+00:00
-- url     : https://prove2.me/theorems/7eebb95a-53a0-4557-aa98-c1552fcfa848
-- title:
--   Chebyshev theta finite certificate: range [52597756, 69355435)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c5a`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $52597756$:
--   $$52589385226535\le 10^6\theta(52597756)\le 52591511472754$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=69355435$:**
--   $$69344896246415\le 10^6\,\theta(69355435)\le 69347654882929$$
--
--   **Pointwise bound.** For every real $x$ with $52597756\le x<69355435$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[52597756,69355435)$ is partitioned into $415$ consecutive prime-interval blocks grouped into $2$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c5a (hprev : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) :
    ((69344896246415 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ≤ (69347654882929 : ℝ)) ∧
    (∀ x : ℝ, (52597756 : ℝ) ≤ x → x < (69355435 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
