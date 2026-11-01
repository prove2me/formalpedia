-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_uniqueness
-- name    : SwitchOptStop.Boundary.theorem_5_1_uniqueness
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T19:21:32.346993+00:00
-- url     : https://prove2.me/theorems/eea1c29d-c671-4e0e-9d04-bfe225140ef7
-- title:
--   Theorem 5.1, p. 15 — uniqueness: the optimal stopping boundary is the only admissible solution of (5.1)
-- statement:
--   Assume the standing setting of the mission: the two-regime linear switching diffusion $(\alpha,X)$ of (2.2) with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$, and suppose the discount rate is constant, $\lambda(\cdot)\equiv\lambda_0>0$. Let $b=(b_\iota)_{\iota\in M}$ be the optimal stopping boundary $b_\iota(x_1)=\inf\{x_2>0: V(\iota,x_1,x_2)=0\}$. Let $c=(c_\iota)_{\iota\in M}$ be admissible, i.e. each $c_\iota$ is bounded, continuous and $[0,\infty)$-valued on $(0,\infty)$ with $H(\iota,(z,c_\iota(z)))\ge0$ for all $z>0$, and suppose $c$ solves (5.1) in place of $b$: for every $\iota$ and $x_1>0$,
--   $$\int_0^\infty\sum_{\kappa\in M}\int_0^\infty\int_0^{c_\kappa(y_1)}e^{-\lambda_0t}\,p_t\big(\iota,x_1,c_\iota(x_1);\kappa,y_1,y_2\big)\,H(\kappa,y)\,dy_2\,dy_1\,dt=0$$
--   (absolutely convergent). Then $c_\iota(z)=b_\iota(z)$ for all $\iota\in M$ and $z>0$. The paper states this uniqueness but its proof (pp. 15–18) does not give the argument.
--
--   As in the goal theorem `SwitchOptStop.Boundary.theorem_5_1`, the triple integrals against the transition density $p_t$ are written in expectation form $\int_0^\infty e^{-\lambda_0 t}\,\mathsf E_{\iota,y}\big[H(\alpha_t,X_t)\mathbf 1\{X^1_t>0,\ 0<X^2_t<c_{\alpha_t}(X^1_t)\}\big]dt$ (the integrand `ieIntegrand`, integrated against $dt\otimes P_\iota$ on $(0,\infty)\times\Omega$), with absolute convergence required explicitly. This is one of the three conclusions of Theorem 5.1, split off verbatim from the goal statement.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 15, Theorem 5.1 (uniqueness in the admissible class)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem theorem_5_1_uniqueness (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (lam0 : ℝ) (hlam0 : 0 < lam0) (hlam : ∀ ι, m.lam ι = lam0) :
    ∀ c : Fin 2 → ℝ → ℝ, Admissible m c →
      (∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 c ι x1) →
      ∀ ι : Fin 2, ∀ z : ℝ, 0 < z → c ι z = bdry m S ι z := by sorry

end SwitchOptStop.Boundary
