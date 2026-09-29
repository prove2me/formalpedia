-- Prove2me | Theorems.Thm_Peng1990_SMP_second_adjoint_equation
-- name    : Peng1990.SMP.second_adjoint_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:36:12.255322+00:00
-- url     : https://prove2.me/theorems/03e6503f-12ec-4531-a472-4eea3010829f
-- title:
--   Eq. (20) — the second-order adjoint process solves the matrix adjoint BSDE
-- statement:
--   Assume (3), let $u$ be admissible with trajectory $y$, let $(p,K)$ be the first-order adjoint process (13) and $(P,Q)$ the second-order adjoint process (17). Then $(P,Q)$ solves
--   $$\begin{aligned}-dP(t)=\Big[&g_x^*(y(t),u(t))P(t)+P(t)g_x(y(t),u(t))+\sum_{j=1}^d\sigma_x^{j*}(y(t),u(t))P(t)\sigma_x^j(y(t),u(t))\\&+\sum_{j=1}^d\sigma_x^{j*}(y(t),u(t))Q_j(t)+\sum_{j=1}^dQ_j(t)\sigma_x^j(y(t),u(t))+H_{xx}(y(t),u(t),p(t),K(t))\Big]dt-\sum_{j=1}^dQ_j(t)\,dB^j(t),\\P(T)=\ &h_{xx}(y(T)).\end{aligned}\tag{20}$$
--
--   The paper obtains (20) "exactly as in [2] and [3]"; it is the second-order adjoint equation of the maximum principle.
--
--   **Formalization Note** The matrix equation is read entrywise; $Q(t)\,dB(t)$ is $\sum_jQ_j\,dB^j$.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 975, (20)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem second_adjoint_equation {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hu : IsAdmissible cp (brownianFiltration hB) P u)
    (hy : SolvesState cp (brownianFiltration hB) P B u y)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hpK : RepresentsI cp (brownianFiltration hB) P B y u p K)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hPQ : RepresentsM cp (brownianFiltration hB) P B y u p K Pm Q) :
    SolvesSecondAdjoint cp (brownianFiltration hB) P B y u p K Pm Q := by sorry

end Peng1990.SMP
