-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c5a2
-- name    : TaoFivePrimes.axler_chain_c5a2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T20:17:16.152512+00:00
-- url     : https://prove2.me/theorems/5acb28ff-993e-4d91-bb23-8484528012dd
-- title:
--   Chebyshev theta finite certificate: range [60984648, 69355435)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c5a2`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $60984648$:
--   $$60976256594858\le 10^6\theta(60984648)\le 60978700593120$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=69355435$:**
--   $$69344896246415\le 10^6\,\theta(69355435)\le 69347654882929$$
--
--   **Pointwise bound.** For every real $x$ with $60984648\le x<69355435$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[60984648,69355435)$ is partitioned into $193$ consecutive prime-interval blocks grouped into $1$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c5a2 (hprev : (60976256594858 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (60984648 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (60984648 : ℝ) ≤ (60978700593120 : ℝ)) :
    ((69344896246415 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ≤ (69347654882929 : ℝ)) ∧
    (∀ x : ℝ, (60984648 : ℝ) ≤ x → x < (69355435 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
