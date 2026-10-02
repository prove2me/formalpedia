-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c4a1
-- name    : TaoFivePrimes.axler_chain_c4a1
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T20:16:33.925983+00:00
-- url     : https://prove2.me/theorems/a94f0417-72cb-4c35-ab54-71c88334a58f
-- title:
--   Chebyshev theta finite certificate: range [17387265, 25762666)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c4a1`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $17387265$:
--   $$17382708166135\le 10^6\theta(17387265)\le 17383459384328$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=25762666$:**
--   $$25755483428246\le 10^6\,\theta(25762666)\le 25756570158533$$
--
--   **Pointwise bound.** For every real $x$ with $17387265\le x<25762666$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[17387265,25762666)$ is partitioned into $590$ consecutive prime-interval blocks grouped into $1$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c4a1 (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) :
    ((25755483428246 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (25762666 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (25762666 : ℝ) ≤ (25756570158533 : ℝ)) ∧
    (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (25762666 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
