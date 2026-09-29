-- Prove2me | Theorems.Thm_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero
-- name    : PowerSeries.exists_eq_X_sub_C_mul_of_tsum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/266927c5-a6b0-57ba-82f0-453ae609da01
-- title:
--   Dividing out a zero of a bounded power series
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F \in L[[X]]$ be a formal power series. Let $\rho, M$ be real numbers with $\rho > 0$, and assume the Gauss-type bound $\|F_n\|\,\rho^n \le M$ for every $n$, where $F_n$ denotes the $n$-th coefficient of $F$. Let $a \in L$ satisfy $\|a\| < \rho$, and assume that the series $\sum_n F_n a^n$ is summable with sum $0$ (the hypothesis is the equality of the unconditional sum `∑' n, PowerSeries.coeff n F * a ^ n` with $0$, which in particular holds vacuously for the value $0$ of a non-summable family, although summability is in fact automatic here). Then there exists $H \in L[[X]]$ such that $F = (X - a)H$ as formal power series, where $a$ is read as the constant series `PowerSeries.C a`, and such that $H$ satisfies the bound $\|H_n\|\,\rho^{n+1} \le M$ for every $n$; that is, $H$ is bounded by $M/\rho$ at radius $\rho$.
--
--   This is the elementary division step of non-archimedean function theory on a disc: a zero $a$ inside the disc of radius $\rho$ may be divided out of a power series bounded at radius $\rho$ at the cost of exactly one factor $\rho$ in the bound, with no use of Weierstrass preparation, coefficient integrality or algebraic closure. It is used in the proof of the iterated bound [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod) and, through it, in the construction of charts on the modular curve ([`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.exists_eq_X_sub_C_mul_of_tsum_eq_zero {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (hFa : ∑' n, PowerSeries.coeff n F * a ^ n = 0) :
    ∃ H : PowerSeries L, F = (PowerSeries.X - PowerSeries.C a) * H ∧
      ∀ n, ‖PowerSeries.coeff n H‖ * ρ ^ (n + 1) ≤ M := by sorry
