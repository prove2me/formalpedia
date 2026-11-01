-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_integral_equation
-- name    : SwitchOptStop.Boundary.theorem_5_1_integral_equation
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T19:21:33.395505+00:00
-- url     : https://prove2.me/theorems/ce83e20e-0e43-4148-a1bd-21de68008c10
-- title:
--   Theorem 5.1 (5.1), p. 15 — the optimal stopping boundary solves the nonlinear integral equation
-- statement:
--   Assume the standing setting of the mission: the two-regime linear switching diffusion $(\alpha,X)$ of (2.2) with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$, and suppose the discount rate is constant, $\lambda(\cdot)\equiv\lambda_0>0$. Let $b=(b_\iota)_{\iota\in M}$ be the optimal stopping boundary $b_\iota(x_1)=\inf\{x_2>0: V(\iota,x_1,x_2)=0\}$. Then $b$ solves the nonlinear integral equation (5.1): for every $\iota\in M$ and every $x_1>0$,
--   $$\int_0^\infty\sum_{\kappa\in M}\int_0^\infty\int_0^{b_\kappa(y_1)}e^{-\lambda_0t}\,p_t\big(\iota,x_1,b_\iota(x_1);\kappa,y_1,y_2\big)\,H(\kappa,y)\,dy_2\,dy_1\,dt=0,$$
--   with the integral absolutely convergent.
--
--   As in the goal theorem `SwitchOptStop.Boundary.theorem_5_1`, the triple integrals against the transition density $p_t$ are written in expectation form $\int_0^\infty e^{-\lambda_0 t}\,\mathsf E_{\iota,y}\big[H(\alpha_t,X_t)\mathbf 1\{X^1_t>0,\ 0<X^2_t<c_{\alpha_t}(X^1_t)\}\big]dt$ (the integrand `ieIntegrand`, integrated against $dt\otimes P_\iota$ on $(0,\infty)\times\Omega$), with absolute convergence required explicitly. This is one of the three conclusions of Theorem 5.1, split off verbatim from the goal statement.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 15, Theorem 5.1, eq. (5.1) (existence part)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem theorem_5_1_integral_equation (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (lam0 : ℝ) (hlam0 : 0 < lam0) (hlam : ∀ ι, m.lam ι = lam0) :
    ∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 (bdry m S) ι x1 := by sorry

end SwitchOptStop.Boundary
