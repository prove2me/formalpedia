-- Prove2me | Theorems.Thm_Peng1990_SMP_first_adjoint_equation
-- name    : Peng1990.SMP.first_adjoint_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:35:42.101977+00:00
-- url     : https://prove2.me/theorems/5c7470ac-966c-47a0-b8e5-0ee67d0e1dc3
-- title:
--   Eq. (19) — the first-order adjoint process is the unique solution of the adjoint BSDE
-- statement:
--   Assume (3), let $u$ be admissible with trajectory $y$, and let $(p,K)$ be the first-order adjoint process of (13). Then $(p,K)$ solves the backward stochastic differential equation
--   $$-dp(t)=\Big[g_x^*(y(t),u(t))p(t)+\sum_{j=1}^d\sigma_x^{j*}(y(t),u(t))K_j(t)+l_x(y(t),u(t))\Big]dt-\sum_{j=1}^dK_j(t)\,dB^j(t),\qquad p(T)=h_x(y(T)),\tag{19}$$
--   and every solution $(p',K')$ of (19) in $L^2_{\mathcal F}(0,T;\mathbb R^n)\times(L^2_{\mathcal F}(0,T;\mathbb R^n))^d$ agrees with $(p,K)$ $dt\otimes dP$-almost everywhere on $[0,T]\times\Omega$.
--
--   The paper takes this from Bensoussan [2], [3]; it identifies the Riesz representer of (13) with the classical first-order adjoint equation.
--
--   **Formalization Note** Solutions are progressive for the natural filtration of $B$; without adaptedness the equation would have trivial pathwise solutions. $K(t)\,dB(t)$ is $\sum_jK_j\,dB^j$.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 974, (19) (cited from Bensoussan [2], [3])

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem first_adjoint_equation {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hu : IsAdmissible cp (brownianFiltration hB) P u)
    (hy : SolvesState cp (brownianFiltration hB) P B u y)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hpK : RepresentsI cp (brownianFiltration hB) P B y u p K) :
    SolvesFirstAdjoint cp (brownianFiltration hB) P B y u p K ∧
    ∀ (p' : ℝ≥0 → Ω → Fin n → ℝ) (K' : Fin d → ℝ≥0 → Ω → Fin n → ℝ),
      SolvesFirstAdjoint cp (brownianFiltration hB) P B y u p' K' →
      ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) cp.T)).prod P),
        p' q.1.toNNReal q.2 = p q.1.toNNReal q.2 ∧
        ∀ j, K' j q.1.toNNReal q.2 = K j q.1.toNNReal q.2 := by sorry

end Peng1990.SMP
