-- Prove2me | Theorems.Thm_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq
-- name    : PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/29fd4a0a-d951-5065-adaf-59c6c82d0476
-- title:
--   Identity principle for bounded power series on a disc
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F,G \in L[[T]]$ be formal power series over $L$. Let $\rho, M, M' \in \mathbb{R}$ with $\rho > 0$, and suppose that $F$ is bounded at radius $\rho$ by $M$, in the sense that $\|\mathrm{coeff}_n F\|\,\rho^n \le M$ for every $n$, and likewise that $\|\mathrm{coeff}_n G\|\,\rho^n \le M'$ for every $n$. Suppose finally that the two series agree as unconditional sums at every point of the open disc of radius $\rho$: for every $z \in L$ with $\|z\| < \rho$, $\sum'_n (\mathrm{coeff}_n F)\, z^n = \sum'_n (\mathrm{coeff}_n G)\, z^n$. Then $F = G$ as formal power series, i.e. all their coefficients coincide. (The sums are Mathlib's `tsum`, so the hypothesis is a genuine equality of sums thanks to the summability supplied by the growth bounds; the hypothesis is imposed only on the open disc $\|z\| < \rho$, not on its closure.)
--
--   This is the identity principle for non-archimedean power series bounded on a disc: a bounded power series over a complete ultrametric field is determined by the function it defines on the open disc of the corresponding radius. It is used to deduce identities of formal power series from identities of their values, for instance multiplicativity of the Taylor shift ([`PowerSeries.taylorShift_mul`](thm.html#PowerSeries.taylorShift_mul)) and the construction of charts in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot); the required summability and the bound on the sums come from [`PowerSeries.summable_and_norm_tsum_coeff_mul_pow_le`](thm.html#PowerSeries.summable_and_norm_tsum_coeff_mul_pow_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (h : ∀ z : L, ‖z‖ < ρ → ∑' n, PowerSeries.coeff n F * z ^ n = ∑' n, PowerSeries.coeff n G * z ^ n) :
    F = G := by sorry
