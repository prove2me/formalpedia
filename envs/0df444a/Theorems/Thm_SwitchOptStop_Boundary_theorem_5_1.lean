-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1
-- name    : SwitchOptStop.Boundary.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:05.467134+00:00
-- url     : https://prove2.me/theorems/d2d62911-eda9-4ba9-b7d8-722890e4e6f4
-- title:
--   Theorem 5.1, p. 15 — with λ ≡ λ0, the stopping boundaries are the unique admissible solution of the integral equation (5.1), and V satisfies (5.2)
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$, and suppose the discount rate is a constant, $\lambda(\cdot)=\lambda_0>0$. Let $p_t(\iota,x;\kappa,y)$ denote the transition density of $(\alpha,X)$. Then the optimal stopping boundary $\{b_\iota\}_{\iota\in M}$ is the unique solution, in the admissible class, of the nonlinear integral equation
--   $$
--   \int_0^\infty\sum_{\kappa\in M}\int_0^\infty\int_0^{b_\kappa(y_1)}e^{-\lambda_0t}\,p_t\big(\iota,x_1,b_\iota(x_1);\kappa,y_1,y_2\big)\,H(\kappa,y)\,dy_2\,dy_1\,dt=0\qquad\text{for all }x_1\in(0,\infty), \tag{5.1}
--   $$
--   where the admissible class consists of all bounded continuous functions $c=(c_\iota)$ with $H(\iota,(z,c_\iota(z)))\ge0$ for all $(\iota,z)\in M\times(0,\infty)$. Moreover the value function has the representation
--   $$
--   V(\iota,x)=\int_0^\infty\sum_{\kappa\in M}\int_0^\infty\int_0^{b_\kappa(y_1)}e^{-\lambda_0t}\,p_t(\iota,x;\kappa,y)\,H(\kappa,y)\,dy_2\,dy_1\,dt. \tag{5.2}
--   $$
--
--   The theorem characterizes the free boundaries of a two-dimensional problem with regime switching by an integral equation, which makes them computable.
--
--   **Formalization Note** The statement has four parts: $b$ is admissible; $b$ solves (5.1) at every $(\iota,x_1)$ with $x_1>0$; every admissible solution equals $b$ on $(0,\infty)$; and (5.2) holds at every $x\in(0,\infty)^2$. The triple integrals against $p_t$ are written as expectations, $\int_0^\infty e^{-\lambda_0t}\mathsf E_{\iota,x}\big[H(\alpha_t,X_t)\mathbf 1\{X^1_t>0,\,0<X^2_t<c_{\alpha_t}(X^1_t)\}\big]dt$, which equal them by Fubini–Tonelli whenever the density exists (the paper asserts its existence without proof); absolute convergence is required explicitly, since a divergent Bochner integral is $0$ in Lean. Admissible functions are taken $[0,\infty)$-valued, because $H$ is only defined on $[0,\infty)^2$. The paper's proof omits the uniqueness argument (p. 18); the statement is posed as printed.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 15, Theorem 5.1, (5.1)–(5.2)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Theorem 5.1 (p. 15): with constant discount rate `λ ≡ λ₀ > 0`, the optimal stopping boundaries
`(b_ι)_ι` are admissible, solve the integral equation (5.1) at every `x₁ > 0`, and are its unique
admissible solution; moreover the value function has the representation (5.2). -/
theorem theorem_5_1 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (lam0 : ℝ) (hlam0 : 0 < lam0) (hlam : ∀ ι, m.lam ι = lam0) :
    Admissible m (bdry m S) ∧
    (∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 (bdry m S) ι x1) ∧
    (∀ c : Fin 2 → ℝ → ℝ, Admissible m c →
      (∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 c ι x1) →
      ∀ ι : Fin 2, ∀ z : ℝ, 0 < z → c ι z = bdry m S ι z) ∧
    (∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      Integrable (ieIntegrand m S lam0 (bdry m S) x) ((volume.restrict (Ioi 0)).prod (Pι S ι)) ∧
      value m S ι x =
        ∫ p, ieIntegrand m S lam0 (bdry m S) x p ∂((volume.restrict (Ioi 0)).prod (Pι S ι))) := by sorry

end SwitchOptStop.Boundary
