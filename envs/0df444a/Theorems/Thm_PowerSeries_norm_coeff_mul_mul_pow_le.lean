-- Prove2me | Theorems.Thm_PowerSeries_norm_coeff_mul_mul_pow_le
-- name    : PowerSeries.norm_coeff_mul_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/2404c868-1a44-5e87-9f77-ce12b6b2a4ad
-- title:
--   Submultiplicativity of the bound at radius ρ
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F,G \in L[[T]]$ be formal power series over $L$. Let $\rho, M, M' \in \mathbb{R}$ with $\rho \ge 0$, and suppose that $\|\,\mathrm{coeff}_n F\,\| \cdot \rho^n \le M$ for every $n \in \mathbb{N}$ and $\|\,\mathrm{coeff}_n G\,\| \cdot \rho^{n} \le M'$ for every $n \in \mathbb{N}$. Then for every $n \in \mathbb{N}$ the $n$-th coefficient of the product satisfies $$\|\,\mathrm{coeff}_n (F G)\,\| \cdot \rho^{n} \le M M'.$$ No positivity is assumed of $M$ or $M'$: it is a consequence of the hypotheses applied at $n = 0$. The bound is asserted coefficientwise for each fixed $n$, not as a statement about a Gauss norm or about convergence of $F$ and $G$ on the disc of radius $\rho$.
--
--   This is the multiplicative half of the elementary estimate saying that the class of power series bounded by $M$ at radius $\rho$ behaves like a Gauss-norm ball: the bound for a product is the product of the bounds. It is used in the construction of local charts on the modular curve, via [`PowerSeries.taylorShift_mul`](thm.html#PowerSeries.taylorShift_mul) and [`PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le`](thm.html#PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le), to keep products of series occurring in a chart computation inside the class to which the evaluation and shift lemmas apply.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_norm_coeff_mul_mul_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.norm_coeff_mul_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (n : ℕ) : ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := by sorry
