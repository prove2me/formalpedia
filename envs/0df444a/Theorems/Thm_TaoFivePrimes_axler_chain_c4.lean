-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c4
-- name    : TaoFivePrimes.axler_chain_c4
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-01T15:25:10.988981+00:00
-- url     : https://prove2.me/theorems/f2fdef52-206e-41c5-bec2-a7f4a23cc9dc
-- title:
--   Chebyshev theta finite certificate: range [17387265, 52597756)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment $k=4$
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $17387265$:
--   $$17382708166135\le 10^6\theta(17387265)\le 17383459384328$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=52597756$:**
--   $$52589385226535\le 10^6\,\theta(52597756)\le 52591511472754$$
--
--   **Pointwise bound.** For every real $x$ with $17387265\le x<52597756$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   As in the first segment, $[17387265,52597756)$ is partitioned into consecutive prime-interval blocks, each block inequality is discharged by kernel computation, and the blocks are chained to give the pointwise bound and the state at the right endpoint.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c4 (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) :
    ((52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) ∧
    (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (52597756 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
