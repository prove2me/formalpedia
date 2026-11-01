-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_representation
-- name    : SwitchOptStop.Boundary.theorem_5_1_representation
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T19:22:01.371903+00:00
-- url     : https://prove2.me/theorems/fbde1751-3706-41ec-ab38-3a1c5e9ab504
-- title:
--   Theorem 5.1 (5.2), p. 15 — integral representation of the value function
-- statement:
--   Assume the standing setting of the mission: the two-regime linear switching diffusion $(\alpha,X)$ of (2.2) with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$, and suppose the discount rate is constant, $\lambda(\cdot)\equiv\lambda_0>0$. Let $b=(b_\iota)_{\iota\in M}$ be the optimal stopping boundary $b_\iota(x_1)=\inf\{x_2>0: V(\iota,x_1,x_2)=0\}$. Then for every $\iota\in M$ and $x\in(0,\infty)^2$ the value function has the representation (5.2)
--   $$V(\iota,x)=\int_0^\infty\sum_{\kappa\in M}\int_0^\infty\int_0^{b_\kappa(y_1)}e^{-\lambda_0t}\,p_t(\iota,x;\kappa,y)\,H(\kappa,y)\,dy_2\,dy_1\,dt,$$
--   with the integral absolutely convergent.
--
--   As in the goal theorem `SwitchOptStop.Boundary.theorem_5_1`, the triple integrals against the transition density $p_t$ are written in expectation form $\int_0^\infty e^{-\lambda_0 t}\,\mathsf E_{\iota,y}\big[H(\alpha_t,X_t)\mathbf 1\{X^1_t>0,\ 0<X^2_t<c_{\alpha_t}(X^1_t)\}\big]dt$ (the integrand `ieIntegrand`, integrated against $dt\otimes P_\iota$ on $(0,\infty)\times\Omega$), with absolute convergence required explicitly. This is one of the three conclusions of Theorem 5.1, split off verbatim from the goal statement.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 15, Theorem 5.1, eq. (5.2)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem theorem_5_1_representation (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (lam0 : ℝ) (hlam0 : 0 < lam0) (hlam : ∀ ι, m.lam ι = lam0) :
    ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      Integrable (ieIntegrand m S lam0 (bdry m S) x) ((volume.restrict (Ioi 0)).prod (Pι S ι)) ∧
      value m S ι x =
        ∫ p, ieIntegrand m S lam0 (bdry m S) x p ∂((volume.restrict (Ioi 0)).prod (Pι S ι)) := by sorry

end SwitchOptStop.Boundary
