-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c4a2
-- name    : TaoFivePrimes.axler_chain_c4a2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T20:16:46.398976+00:00
-- url     : https://prove2.me/theorems/90147623-974a-4727-aed1-4cef46b1d0f2
-- title:
--   Chebyshev theta finite certificate: range [25762666, 34129386)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c4a2`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $25762666$:
--   $$25755483428246\le 10^6\theta(25762666)\le 25756570158533$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=34129386$:**
--   $$34123262759331\le 10^6\,\theta(34129386)\le 34124678342292$$
--
--   **Pointwise bound.** For every real $x$ with $25762666\le x<34129386$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[25762666,34129386)$ is partitioned into $422$ consecutive prime-interval blocks grouped into $1$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c4a2 (hprev : (25755483428246 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (25762666 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (25762666 : ℝ) ≤ (25756570158533 : ℝ)) :
    ((34123262759331 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ≤ (34124678342292 : ℝ)) ∧
    (∀ x : ℝ, (25762666 : ℝ) ≤ x → x < (34129386 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
