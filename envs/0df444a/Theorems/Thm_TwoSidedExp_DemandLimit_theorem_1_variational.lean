-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_theorem_1_variational
-- name    : TwoSidedExp.DemandLimit.theorem_1_variational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:36.538786+00:00
-- url     : https://prove2.me/theorems/504c31de-c2ac-4877-8c96-3b58a763cc2d
-- title:
--   Theorem 1, p. 12 (second part) — s∗ is the unique minimiser of W over 0 < s ≤ ρ
-- statement:
--   Under the standing assumptions, with $\lambda>0$ and $\tau>0$, let
--   $$W(s)=\sum_\gamma\lambda\phi_\gamma\log\Big(\epsilon_\gamma+\sum_\theta\alpha_\gamma(\theta)v_\gamma(\theta)s(\theta)\Big)-\sum_\theta\tau\nu(\theta)\rho(\theta)\log s(\theta)+\sum_\theta\tau\nu(\theta)s(\theta).$$
--   A vector $s$ minimises $W$ over the set $\{s':0<s'(\theta)\le\rho(\theta)\ \forall\theta\}$ (and lies in it) if and only if $s$ is a steady state of the mean-field system, i.e. $s\in\mathcal S$ and $(\rho(\theta)-s(\theta))\tau\nu(\theta)=\lambda\sum_\gamma\phi_\gamma p_\gamma(\theta\mid s)$ for all $\theta$.
--
--   Together with the uniqueness of the steady state, this says that $s^*$ is the unique minimiser of $W$: the steady state has a variational characterisation.
--
--   **Formalization Note** The paper writes the constraint $0\le s(\theta)\le\rho(\theta)$ (11), where $W=+\infty$ on the boundary $s(\theta)=0$. Lean's `Real.log 0 = 0` would make $W$ finite there, so the feasible set is $0<s(\theta)\le\rho(\theta)$; the paper's own proof (Step 3, p. A1) shows that the minimum is not attained on the boundary. In (10) the printed $\tau(\theta)$ outside $\sum_\theta$ is read inside the sums, as in (30), and $\lambda_\gamma=\lambda\phi_\gamma$.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 12, Theorem 1, (10)–(11); p. A1, (30)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Theorem 1, p. 12 (second part): a state `s` with `0 < s(θ) ≤ ρ(θ)` minimises `W` of (10) over
`{s' : 0 < s'(θ) ≤ ρ(θ)}` if and only if it is a steady state of (9). -/
theorem theorem_1_variational {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (lam tau : ℝ) (hlam : 0 < lam) (htau : 0 < tau) (s : Θ → ℝ) :
    ((∀ θ, 0 < s θ ∧ s θ ≤ M.sys.ρ θ) ∧
        ∀ s' : Θ → ℝ, (∀ θ, 0 < s' θ ∧ s' θ ≤ M.sys.ρ θ) →
          M.sys.W lam tau s ≤ M.sys.W lam tau s') ↔
      M.sys.IsSteady lam tau s := by sorry

end TwoSidedExp.DemandLimit
