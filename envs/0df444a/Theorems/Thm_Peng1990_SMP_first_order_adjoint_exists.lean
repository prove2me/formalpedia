-- Prove2me | Theorems.Thm_Peng1990_SMP_first_order_adjoint_exists
-- name    : Peng1990.SMP.first_order_adjoint_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:33:35.135989+00:00
-- url     : https://prove2.me/theorems/a4211921-cebb-40b8-a024-6487d730fe32
-- title:
--   Eq. (13) — existence and uniqueness of the first-order adjoint process $(p,K)$
-- statement:
--   Assume (3), let $u$ be admissible with trajectory $y$, and use the linear system (12). There is a pair
--   $$(p,K)\in L^2_{\mathcal F}(0,T;\mathbb R^n)\times\big(L^2_{\mathcal F}(0,T;\mathbb R^n)\big)^d,\qquad K=(K_1,\dots,K_d),$$
--   such that for all $(\varphi,\psi)\in L^2_{\mathcal F}(0,T;\mathbb R^n)\times(L^2_{\mathcal F}(0,T;\mathbb R^n))^d$ and the solution $z$ of (12),
--   $$E\int_0^T\Big[(p(t),\varphi(t))+\sum_{j=1}^d(K_j(t),\psi_j(t))\Big]dt=E\int_0^Tl_x(t)z(t)\,dt+E\big(h_x(y(T))z(T)\big),\tag{13}$$
--   and any two such pairs agree $dt\otimes dP$-almost everywhere on $[0,T]\times\Omega$.
--
--   The paper obtains $(p,K)$ from the Riesz representation of the continuous linear functional $I(\varphi,\psi)$; $(p,K)$ is the first-order adjoint process.
--
--   **Formalization Note** The section's pair $(y,u)$ is optimal; the statement does not use optimality and is made for every admissible pair. Uniqueness is uniqueness in the Hilbert space $L^2_{\mathcal F}$, i.e. up to $dt\otimes dP$-null sets.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, pp. 971–972, (12), (13)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem first_order_adjoint_exists {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hu : IsAdmissible cp (brownianFiltration hB) P u)
    (hy : SolvesState cp (brownianFiltration hB) P B u y) :
    (∃ (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ),
      RepresentsI cp (brownianFiltration hB) P B y u p K) ∧
    ∀ (p p' : ℝ≥0 → Ω → Fin n → ℝ) (K K' : Fin d → ℝ≥0 → Ω → Fin n → ℝ),
      RepresentsI cp (brownianFiltration hB) P B y u p K →
      RepresentsI cp (brownianFiltration hB) P B y u p' K' →
      ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) cp.T)).prod P),
        p q.1.toNNReal q.2 = p' q.1.toNNReal q.2 ∧
        ∀ j, K j q.1.toNNReal q.2 = K' j q.1.toNNReal q.2 := by sorry

end Peng1990.SMP
