-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c2
-- name    : TaoFivePrimes.axler_chain_c2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T15:25:01.979025+00:00
-- url     : https://prove2.me/theorems/9440a843-cbbc-4d7d-b5ee-dc4cd075af20
-- title:
--   Chebyshev theta finite certificate: range [154970, 1699362)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment $k=2$
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $154970$:
--   $$154635160747\le 10^6\theta(154970)\le 154642599361$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=1699362$:**
--   $$L\le 10^6\,\theta(1699362)\le U$$
--   with $L,U$ the integers appearing in the statement.
--
--   **Pointwise bound.** For every real $x$ with $154970\le x<1699362$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   As in the first segment, $[154970,1699362)$ is partitioned into consecutive prime-interval blocks, each block inequality is discharged by kernel computation, and the blocks are chained to give the pointwise bound and the state at the right endpoint.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c2 (hprev : (154635160747 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ≤ (154642599361 : ℝ)) :
    ((1697867131810 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ≤ (1697951293771 : ℝ)) ∧
    (∀ x : ℝ, (154970 : ℝ) ≤ x → x < (1699362 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
