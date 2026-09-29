-- Prove2me | Theorems.Thm_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod
-- name    : PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/8bae8d7b-40fb-57a4-ab90-61e37c23c029
-- title:
--   One-sided Schwarz–Jensen bound over a prescribed multiset of zeros
-- statement:
--   Let $L$ be a complete nontrivially normed field whose norm is ultrametric, let $F\in L[[T]]$, and let $\rho,M$ be reals with $\rho>0$ and $\|a_n\|\rho^n\le M$ for every $n$, where $a_n$ denotes the $n$-th coefficient of $F$. Let $S$ be a multiset of elements of $L$ such that every $w\in S$ satisfies $\|w\|<\rho$ and such that, for every $w\in S$, the multiplicity of $w$ in $S$, viewed in $\mathbb{N}\cup\{\infty\}$, is at most the order of the power series whose $n$-th coefficient is $\sum'_{k}a_{n+k}\binom{n+k}{n}w^{k}$, i.e. the Taylor shift of $F$ at $w$ (the order being $\infty$ if that series vanishes identically). Then for every $z\in L$ with $\|z\|<\rho$,
--   $$\Bigl\|\sum_{n}{}' a_n z^n\Bigr\|\le M\cdot\prod_{w\in S}\frac{\|z-w\|}{\rho},$$ the product being the product of the multiset obtained by applying $w\mapsto \|z-w\|/\rho$ to $S$. All infinite sums are unconditional sums, taking the value $0$ if the family is not summable.
--
--   This is the one-sided Schwarz–Jensen inequality for a bounded power series on the open disc of radius $\rho$, in the form where the zeros are given in advance: $S$ is any multiset of points of the disc at which $F$ vanishes to at least the prescribed multiplicity, with no requirement that $L$ be algebraically closed and no appeal to Weierstrass preparation. It is used in the construction of disc charts on the modular curve, via [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot), and in [`PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero`](thm.html#PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Classical in

theorem PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (S : Multiset L) (hS1 : ∀ w ∈ S, ‖w‖ < ρ)
    (hS : ∀ w ∈ S, (S.count w : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order)
    (z : L) (hz : ‖z‖ < ρ) :
    ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M * (S.map fun w => ‖z - w‖ / ρ).prod := by sorry
