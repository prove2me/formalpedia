-- Prove2me | Theorems.Thm_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt
-- name    : PowerSeries.tsum_coeff_mul_mul_pow_eq_of_norm_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/e8ec9e59-39c4-5b49-87b1-3e77b7920599
-- title:
--   Evaluation of power series on a disc is multiplicative
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F, G \in L[[T]]$ be formal power series. Let $\rho, M, M' \in \mathbb{R}$ with $\rho > 0$, and assume the growth bounds $\|\mathrm{coeff}_n(F)\|\,\rho^n \le M$ and $\|\mathrm{coeff}_n(G)\|\,\rho^n \le M'$ for every $n \in \mathbb{N}$ (no separate positivity of $M$ or $M'$ is assumed; it follows from the case $n = 0$). Let $z \in L$ satisfy $\|z\| < \rho$. Then the three unconditional sums $\sum_n \mathrm{coeff}_n(FG)\, z^n$, $\sum_n \mathrm{coeff}_n(F)\, z^n$ and $\sum_n \mathrm{coeff}_n(G)\, z^n$ satisfy $$\sum_n \mathrm{coeff}_n(FG)\, z^n = \Bigl(\sum_n \mathrm{coeff}_n(F)\, z^n\Bigr)\Bigl(\sum_n \mathrm{coeff}_n(G)\, z^n\Bigr).$$ Thus evaluation at a point of the open disc of radius $\rho$ is multiplicative on series bounded at radius $\rho$, the statement being about `tsum` values rather than about a separately formulated convergence assertion.
--
--   This is the Cauchy product formula for power series over a complete normed field, in the form needed for the formal-series calculus on discs: series bounded at radius $\rho$ may be evaluated at any point of the open disc of radius $\rho$, and evaluation respects multiplication of series. It is used in the analysis of charts on modular curves, in the estimate [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod) for norms of evaluated products, and in [`PowerSeries.taylorShift_mul`](thm.html#PowerSeries.taylorShift_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.tsum_coeff_mul_mul_pow_eq_of_norm_lt {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (z : L) (hz : ‖z‖ < ρ) :
    ∑' n, PowerSeries.coeff n (F * G) * z ^ n
      = (∑' n, PowerSeries.coeff n F * z ^ n) * ∑' n, PowerSeries.coeff n G * z ^ n := by sorry
