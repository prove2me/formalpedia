-- Prove2me | Theorems.Thm_PowerSeries_taylorShift_add
-- name    : PowerSeries.taylorShift_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/9b6978bc-ed4c-5199-922c-6a07ee593fc4
-- title:
--   Additivity of the Taylor shift of bounded power series
-- statement:
--   Let $L$ be a nontrivially normed field which is complete and whose distance is ultrametric, and let $F, G \in L[[T]]$ be formal power series. Let $\rho, M, M'$ be reals with $\rho > 0$, and assume the coefficientwise bounds $\|\mathrm{coeff}_n F\|\,\rho^n \le M$ and $\|\mathrm{coeff}_n G\|\,\rho^n \le M'$ for all $n$. Let $a \in L$ with $\|a\| < \rho$. Form, for any power series $H$, the shifted series whose $n$-th coefficient is the sum of the series $\sum_{k} \mathrm{coeff}_{n+k}(H)\binom{n+k}{n} a^k$ (the `tsum`, i.e. the value of the unconditional sum when the family is summable and $0$ otherwise). The conclusion is that this construction applied to $F + G$ equals the sum of the constructions applied to $F$ and to $G$: as elements of $L[[T]]$,
--   $$\mathrm{mk}\Big(n \mapsto \sum_{k}' \mathrm{coeff}_{n+k}(F+G)\binom{n+k}{n}a^k\Big) = \mathrm{mk}\Big(n \mapsto \sum_{k}' \mathrm{coeff}_{n+k}(F)\binom{n+k}{n}a^k\Big) + \mathrm{mk}\Big(n \mapsto \sum_{k}' \mathrm{coeff}_{n+k}(G)\binom{n+k}{n}a^k\Big).$$
--   The growth hypotheses on $F$ and $G$ and the bound $\|a\| < \rho$ serve to guarantee summability of the defining series, so that the sums may legitimately be split.
--
--   This is the additivity of the Taylor shift (re-expansion about a point $a$ of the open disc) on power series of bounded Gauss norm at radius $\rho$ over a complete ultrametric field. Together with multiplicativity it makes the shift a ring homomorphism on such series; it is used in [`PowerSeries.taylorShift_sum_C_mul_prod`](thm.html#PowerSeries.taylorShift_sum_C_mul_prod) and in the construction of charts on modular curves in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_taylorShift_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.taylorShift_add {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F + G) * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
        + (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G * ((n + k).choose n : L) * a ^ k) := by sorry
