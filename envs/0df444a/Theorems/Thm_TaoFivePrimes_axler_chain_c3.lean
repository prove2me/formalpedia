-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c3
-- name    : TaoFivePrimes.axler_chain_c3
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T15:25:11.526818+00:00
-- url     : https://prove2.me/theorems/5ce418f9-e0d9-4a6b-976b-a6918b34486f
-- title:
--   Chebyshev theta finite certificate: range [1699362, 17387265)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment $k=3$
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $1699362$:
--   $$1697867131810\le 10^6\theta(1699362)\le 1697951293771$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=17387265$:**
--   $$17382708166135\le 10^6\,\theta(17387265)\le 17383459384328$$
--
--   **Pointwise bound.** For every real $x$ with $1699362\le x<17387265$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   As in the first segment, $[1699362,17387265)$ is partitioned into consecutive prime-interval blocks, each block inequality is discharged by kernel computation, and the blocks are chained to give the pointwise bound and the state at the right endpoint.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c3 (hprev : (1697867131810 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ≤ (1697951293771 : ℝ)) :
    ((17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) ∧
    (∀ x : ℝ, (1699362 : ℝ) ≤ x → x < (17387265 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
