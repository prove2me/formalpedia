-- Prove2me | Theorems.Thm_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le
-- name    : PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d4e320fa-2042-505f-b2a0-e784052b2064
-- title:
--   Gauss-norm bound for sums of scaled products of power series
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose norm is ultrametric, let $\iota$ be a type and $s$ a finite subset of $\iota$, let $c : \iota \to L$ be scalars, let $\kappa$ be a finite type and let $F_{ij} \in L[[T]]$ be formal power series indexed by $i \in \iota$ and $j \in \kappa$. Let $\rho \ge 0$ and $B \ge 0$ be real numbers. Assume that each factor is bounded by $1$ at radius $\rho$ in the sense that $\lVert \mathrm{coeff}_n (F_{ij})\rVert \, \rho^n \le 1$ for every $i \in s$, every $j \in \kappa$ and every $n \in \mathbb{N}$, and that $\lVert c_i \rVert \le B$ for every $i \in s$. Then for every $n \in \mathbb{N}$ the $n$-th coefficient of the power series $\sum_{i \in s} C(c_i) \prod_{j \in \kappa} F_{ij}$, where $C(c_i)$ denotes the constant power series $c_i$ and the product is over the whole finite type $\kappa$, satisfies $\lVert \mathrm{coeff}_n\bigl(\sum_{i \in s} C(c_i) \prod_{j} F_{ij}\bigr)\rVert \, \rho^n \le B$. The bound is uniform in $n$, i.e. it is the Gauss-norm bound at radius $\rho$ for the whole combination.
--
--   This is the statement that the Gauss norm at radius $\rho$ over a complete ultrametric field is submultiplicative on products and non-archimedean on sums: a finite sum of products of factors of Gauss norm at most $1$, scaled by coefficients of norm at most $B$, again has Gauss norm at most $B$. It supplies the boundedness hypothesis needed for the recentring and Schwarz–Jensen estimates on a disc, and is used by [`PowerSeries.taylorShift_sum_C_mul_prod`](thm.html#PowerSeries.taylorShift_sum_C_mul_prod) and [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ B)
    (n : ℕ) :
    ‖PowerSeries.coeff n (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j)‖ * ρ ^ n ≤ B := by sorry
