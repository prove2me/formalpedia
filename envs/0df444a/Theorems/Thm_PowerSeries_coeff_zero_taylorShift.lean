-- Prove2me | Theorems.Thm_PowerSeries_coeff_zero_taylorShift
-- name    : PowerSeries.coeff_zero_taylorShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/1befde95-6266-5cd1-92b5-463cea094d5f
-- title:
--   Constant coefficient of the Taylor shift equals F(a)
-- statement:
--   Let $L$ be a nontrivially normed field which is complete and whose distance is ultrametric, let $F \in L[[T]]$ be a formal power series over $L$, and let $a \in L$. Form the power series whose $n$-th coefficient is the infinite sum $\sum'_{k}\; \mathrm{coeff}_{n+k}(F)\cdot \binom{n+k}{n}\cdot a^{k}$, the coefficients of the Taylor shift of $F$ at $a$ (here $\sum'$ is the unconditional sum in $L$, which takes the value $0$ when the family is not summable, and $\binom{n+k}{n}$ is the natural-number binomial coefficient mapped into $L$). The assertion is that the coefficient of index $0$ of this power series equals $\sum'_{k}\; \mathrm{coeff}_{k}(F)\cdot a^{k}$, i.e. the value $F(a)$ written as a plain unconditional sum. No summability or convergence hypothesis is imposed: both sides are literally the same sum, since $\binom{0+k}{0}=1$ and $0+k=k$.
--
--   This is the normalisation statement identifying the constant term of the non-archimedean Taylor shift of $F$ at $a$ with the value $F(a)$; it converts the assertion that the shifted series has positive order into the assertion $F(a)=0$, the shape in which a zero is divided out. It is used in the estimates [`PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero`](thm.html#PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero) and [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod), and in the construction of charts in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_coeff_zero_taylorShift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.coeff_zero_taylorShift {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) (a : L) :
    PowerSeries.coeff 0 (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
      = ∑' k, PowerSeries.coeff k F * a ^ k := by sorry
