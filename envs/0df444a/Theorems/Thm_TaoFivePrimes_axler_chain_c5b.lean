-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c5b
-- name    : TaoFivePrimes.axler_chain_c5b
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T18:32:27.853323+00:00
-- url     : https://prove2.me/theorems/26d21c82-a365-439c-927c-fe817d7a5f9e
-- title:
--   Chebyshev theta finite certificate: range [69355435, 77727216)
-- statement:
--   ## Chebyshev $\theta$ certificate, segment `axler_chain_c5b`
--
--   Write $\theta(x)=\sum_{p\le x}\log p$. Assume as input the previous segment state at the integer $69355435$:
--   $$69344896246415\le 10^6\theta(69355435)\le 69347654882929$$
--
--   This segment folds the next block chain and exports:
--
--   **State at $T=77727216$:**
--   $$77716973602484\le 10^6\,\theta(77727216)\le 77720044899979$$
--
--   **Pointwise bound.** For every real $x$ with $69355435\le x<77727216$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The interval $[69355435,77727216)$ is partitioned into $171$ consecutive prime-interval blocks grouped into $1$ chained groups; each block inequality is discharged by kernel computation and the groups are chained to give the pointwise bound and the state at the right endpoint. This segment is independent of the others: the previous state is a hypothesis.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c5b (hprev : (69344896246415 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ≤ (69347654882929 : ℝ)) :
    ((77716973602484 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (77727216 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (77727216 : ℝ) ≤ (77720044899979 : ℝ)) ∧
    (∀ x : ℝ, (69355435 : ℝ) ≤ x → x < (77727216 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
