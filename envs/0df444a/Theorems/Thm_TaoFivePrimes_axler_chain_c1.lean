-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_chain_c1
-- name    : TaoFivePrimes.axler_chain_c1
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-01T15:24:53.885718+00:00
-- url     : https://prove2.me/theorems/83c59989-a27b-4b4f-8d46-c149eae1e188
-- title:
--   Chebyshev theta finite certificate: anchor state and range [70111, 154970)
-- statement:
--   ## Chebyshev $\theta$ certificate: anchor state and first segment
--
--   Write $\theta(x)=\sum_{p\le x}\log p$ and $T_1=154970$. The verified interval table for $\theta$ on $[70111,10^8)$ begins with a carry block and one folded block chain, and this theorem exports its two outputs:
--
--   **Anchor state.** With $10^6\theta(T_1)$ bracketed by integers,
--   $$154635160747\le 10^6\,\theta(154970)\le 154642599361 .$$
--
--   **Pointwise bound.** For every real $x$ with $70111\le x<154970$,
--   $$|\theta(x)-x|<\frac{100x}{(\log x)^4}.$$
--
--   The bound is established by folding $5309$ consecutive prime-interval blocks: the interval $[70111,154970)$ is partitioned into blocks $[a,b)$ on which $\theta$ is trapped between rational bounds built from the primes in the block, and each block inequality is discharged by kernel computation. Chaining the blocks gives the pointwise bound on the whole segment.
-- source:
--   Decomposition of the platform target TaoFivePrimes.axler_theta_log_four_finite_certificate (finite verification of Axler's bound |theta(x) - x| < 100 x / (log x)^4 on [70111, 10^8)); block data generated and exact-checked against the source certificate, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

theorem TaoFivePrimes.axler_chain_c1 :
    ((154635160747 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ≤ (154642599361 : ℝ)) ∧
    (∀ x : ℝ, (70111 : ℝ) ≤ x → x < (154970 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by sorry
