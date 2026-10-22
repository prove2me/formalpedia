-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_theorem_1
-- name    : TwoSidedExp.DemandLimit.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:30.13133+00:00
-- url     : https://prove2.me/theorems/b50097db-d205-401f-bfdc-3545a408b875
-- title:
--   Theorem 1, p. 12 — the mean-field steady-state equation (9) has a unique solution in S, and it is interior
-- statement:
--   Consider the base mean-field system of a two-sided marketplace under the standing assumptions, with arrival rate $\lambda>0$ and holding scale $\tau>0$. Then the flow-balance system
--   $$(\rho(\theta)-s(\theta))\,\tau\nu(\theta)=\lambda\sum_\gamma\phi_\gamma\,p_\gamma(\theta\mid s)\qquad(\theta\in\Theta)$$
--   has exactly one solution $s^*$ in the state space $\mathcal S=\{s:0\le s(\theta)\le\rho(\theta)\}$, and this solution satisfies
--   $$0<s^*(\theta)<\rho(\theta)\qquad\text{for every }\theta\in\Theta.$$
--
--   The steady state $s^*$ is the object on which every booking rate of the paper is evaluated.
--
--   **Formalization Note** Only the steady-state part of Theorem 1 is stated; the sentence on global asymptotic stability of the ODE (8) is not formalized. $\tau(\theta)$ is $\tau\nu(\theta)$.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 12, Theorem 1, (9)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Theorem 1, p. 12 (steady-state part): for every `λ, τ > 0` the base mean-field system has a
unique steady state `s* ∈ S` solving (9), and `0 < s*(θ) < ρ(θ)` for every `θ`. -/
theorem theorem_1 {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing)
    (lam tau : ℝ) (hlam : 0 < lam) (htau : 0 < tau) :
    (∃! s : Θ → ℝ, M.sys.IsSteady lam tau s) ∧
      ∀ s : Θ → ℝ, M.sys.IsSteady lam tau s → ∀ θ, 0 < s θ ∧ s θ < M.sys.ρ θ := by sorry

end TwoSidedExp.DemandLimit
