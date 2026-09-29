-- Prove2me | Theorems.Thm_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le
-- name    : PowerSeries.summable_and_norm_tsum_coeff_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/5dff097a-540d-5fcb-a765-c46c26c5b676
-- title:
--   Convergence and bound on the open disc of radius ρ
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F \in L[[T]]$ be a formal power series in one variable over $L$. Suppose given real numbers $\rho, M$ with $\rho > 0$ such that $\|\mathrm{coeff}_n(F)\| \cdot \rho^n \le M$ for every $n \in \mathbb{N}$, i.e. the coefficients of $F$ satisfy the bound $M$ at radius $\rho$. Then for every $z \in L$ with $\|z\| < \rho$ two assertions hold simultaneously: first, the family $n \mapsto \mathrm{coeff}_n(F)\, z^n$ indexed by $\mathbb{N}$ is summable in $L$; second, the value of the sum satisfies $\bigl\| \sum_{n} \mathrm{coeff}_n(F)\, z^n \bigr\| \le M$, with the same constant $M$ as in the coefficient hypothesis. No nonnegativity assumption on $M$ is imposed: it follows from the hypothesis at $n = 0$, since $\|\mathrm{coeff}_0(F)\| \le M$.
--
--   This is the basic convergence-and-bound statement for a power series presented with an explicit radius and an explicit coefficient bound, as opposed to a Gauss-norm or restrictedness hypothesis; the conclusion is the ultrametric maximum bound on the open disc of radius $\rho$. It is used when chart series are evaluated at points of their discs, and is cited by [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot), [`PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq`](thm.html#PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq) and [`PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod`](thm.html#PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.summable_and_norm_tsum_coeff_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (z : L) (hz : ‖z‖ < ρ) :
    Summable (fun n => PowerSeries.coeff n F * z ^ n) ∧ ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M := by sorry
