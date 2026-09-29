-- Prove2me | Theorems.Thm_PowerSeries_norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero
-- name    : PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/6fa4d876-e911-5d8f-b55a-283bf46a3e0a
-- title:
--   Regularised one-sided Schwarz–Jensen bound on a disc
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, let $F \in L[[T]]$ be a formal power series, and let $\rho, M$ be reals with $\rho > 0$ such that $\|\mathrm{coeff}_n F\|\,\rho^{n} \le M$ for every $n$. Let $e$ be a natural number such that $\mathrm{coeff}_n F = 0$ for all $n < e$. Let $S$ be a multiset of elements of $L$ such that every $w \in S$ satisfies $\|w\| < \rho$ and $w \ne 0$, and such that for every $w \in S$ the multiplicity $\mathrm{count}_S(w)$, viewed in $\mathbb{N}\cup\{\infty\}$, is at most the order of the power series whose $n$-th coefficient is $\sum_{k}' \mathrm{coeff}_{n+k}(F)\binom{n+k}{n} w^{k}$, that is, of the Taylor shift of $F$ to the point $w$ (the sums being unconditional sums in $L$). Then
--   $$\|\mathrm{coeff}_e F\|\,\rho^{e} \;\le\; M \prod_{w \in S} \frac{\|w\|}{\rho},$$
--   the product being over the multiset $S$ with multiplicities.
--
--   This is the one-sided Schwarz–Jensen inequality on a disc of radius $\rho$ over a complete ultrametric field, in the form regularised at the centre: when $F$ vanishes at the centre to order at least $e$, the normalised leading quantity $\|\mathrm{coeff}_e F\|\rho^{e}$ is bounded by the bound at radius $\rho$ times the product of the normalised distances from the centre to the prescribed zeros. It is used in the analytic input to the Jensen-type estimates on disc charts of a modular curve, through [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot) and [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Classical in

theorem PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (e : ℕ) (he : ∀ n < e, PowerSeries.coeff n F = 0)
    (S : Multiset L) (hS1 : ∀ w ∈ S, ‖w‖ < ρ) (hS0 : ∀ w ∈ S, w ≠ 0)
    (hS : ∀ w ∈ S, (S.count w : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order) :
    ‖PowerSeries.coeff e F‖ * ρ ^ e ≤ M * (S.map fun w => ‖w‖ / ρ).prod := by sorry
