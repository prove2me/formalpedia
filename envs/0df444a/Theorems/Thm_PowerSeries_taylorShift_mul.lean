-- Prove2me | Theorems.Thm_PowerSeries_taylorShift_mul
-- name    : PowerSeries.taylorShift_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/aeeb133a-ae32-547c-b394-1f99b08a54ff
-- title:
--   Multiplicativity of the Taylor shift on a disc
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose norm is ultrametric, let $F,G \in L[[T]]$ be formal power series, let $\rho, M, M' \in \mathbb{R}$ with $\rho > 0$, and assume the coefficient bounds $\|\mathrm{coeff}_n F\|\,\rho^n \le M$ and $\|\mathrm{coeff}_n G\|\,\rho^n \le M'$ for every $n \in \mathbb{N}$. Let $a \in L$ with $\|a\| < \rho$. For a power series $H$ write $H_a$ for the series whose $n$-th coefficient is the sum $\sum_{k}' \mathrm{coeff}_{n+k}(H)\binom{n+k}{n} a^k$ (a `tsum`, so interpreted as $0$ if the family is not summable; under the hypotheses above the relevant families are in fact summable). The assertion is the identity of formal power series $(F\cdot G)_a = F_a \cdot G_a$, that is, the series built from the coefficients of the product $F G$ by the shift formula equals the product of the two series built the same way from $F$ and from $G$ separately. The bounds $M$ and $M'$ enter only through the hypotheses; no bound on the conclusion is asserted.
--
--   This is the multiplicativity of the Taylor shift (recentring) operation on power series bounded at radius $\rho$ over a complete ultrametric field. It is used in the non-archimedean function theory underlying the construction of charts on modular curves, where the shift of a product of series must be recognised as the product of the shifts, and is cited by [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot) and by the norm estimates [`PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero`](thm.html#PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero) and [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_taylorShift_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.taylorShift_mul {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F * G) * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
        * (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G * ((n + k).choose n : L) * a ^ k) := by sorry
