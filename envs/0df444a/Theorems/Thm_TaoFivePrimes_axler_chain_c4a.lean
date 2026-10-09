-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c4a
-- name    : TaoFivePrimes.axler_chain_c4a
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T18:32:07.904359+00:00
-- url     : https://prove2.me/theorems/026b45ae-9b1a-4149-8ed0-2451c13c5393
-- title:
--   Chebyshev theta finite certificate: range [17387265, 34129386)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c4a`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $17387265$:
--   $$17382708166135\le 10^6\theta(17387265)\le 17383459384328$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=34129386$:**
--   $$34123262759331\le 10^6\,\theta(34129386)\le 34124678342292$$
--
--   **Pointwise bound.** For every real $x$ with $17387265\le x<34129386$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[17387265,34129386)$ is partitioned into $1012$ consecutive prime-interval blocks grouped into $2$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c4a (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) :
    ((34123262759331 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ≤ (34124678342292 : ℝ)) ∧
    (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (34129386 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
