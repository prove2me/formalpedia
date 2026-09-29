-- Prove2me | Theorems.Thm_PowerSeries_taylorShift_X_sub_C
-- name    : PowerSeries.taylorShift_X_sub_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/c93f6cf0-77c0-5770-8c27-f189e2cc388f
-- title:
--   Taylor shift of X-w at a equals (a-w)+X
-- statement:
--   Let $L$ be a nontrivially normed field which is complete and whose distance is ultrametric, and let $w, a \in L$. Form the formal power series over $L$ whose $n$-th coefficient is the sum of the series $\sum_{k=0}^{\infty} \operatorname{coeff}_{n+k}(X - C(w)) \cdot \binom{n+k}{n} \cdot a^{k}$, where $X - C(w)$ is the power series with constant term $-w$ and linear coefficient $1$, $\binom{n+k}{n}$ is interpreted in $L$ via the canonical map from $\mathbb{N}$, and the infinite sum is the unconditional sum (`tsum`) in $L$, taking the value $0$ when the family is not summable. The assertion is that this power series equals $C(a-w) + X$, i.e. the series with constant term $a - w$, linear coefficient $1$ and all higher coefficients zero. In other words, the coefficientwise Taylor-shift formula applied to the linear series $X - w$ at the point $a$ returns the linear series $(a-w) + X$. The proof uses neither the completeness nor the ultrametricity hypothesis: for each $n$ the defining family has only finitely many nonzero terms.
--
--   This is the Taylor shift (change of centre) of a linear polynomial on a disc in non-archimedean function theory, recorded here in the coefficientwise form used throughout the project's treatment of power series over a complete ultrametric field. It is used in the estimate [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod) and in the construction of charts in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_taylorShift_X_sub_C.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.taylorShift_X_sub_C {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (w a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (PowerSeries.X - PowerSeries.C w) * ((n + k).choose n : L) * a ^ k)
      = PowerSeries.C (a - w) + PowerSeries.X := by sorry
