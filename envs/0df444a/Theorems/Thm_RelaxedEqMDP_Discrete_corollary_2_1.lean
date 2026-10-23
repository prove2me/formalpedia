-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_corollary_2_1
-- name    : RelaxedEqMDP.Discrete.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:38.441397+00:00
-- url     : https://prove2.me/theorems/fea730f0-55e7-46e7-9409-dda1f4a81c36
-- title:
--   Corollary 2.1, p. 7 — $y=V^\pi_\lambda$ for a regular relaxed equilibrium $\pi$ iff $\Psi_\lambda(y)=y$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumption 2.1 hold and $\lambda>0$. For every $y\in\mathbb R^d$,
--   $$y=V^\pi_\lambda\ \text{for some regular relaxed equilibrium }\pi\in\Pi_r\iff\Psi_\lambda(y)=y,$$
--   where $\Psi_\lambda(y)=V^{\Gamma_\lambda(y,\cdot)}_\lambda$. In particular, $\Psi_\lambda(y)=y$ implies that $\Gamma_\lambda(y,\cdot)\in\Pi_r$ is a regular relaxed equilibrium.
--
--   This reduces the existence of regular relaxed equilibria to a fixed point of a map on $\mathbb R^d$.
--
--   **Formalization Note** Measurability of $u\mapsto f(t,i,u)$ and $u\mapsto p^u_{ij}$ is assumed.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 7, Corollary 2.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Corollary 2.1, p. 7: under Assumption 2.1 and `λ > 0`, for any `y ∈ ℝ^d`,
`y = V^π_λ` for some regular relaxed equilibrium `π` iff `Ψ_λ(y) = y`; in particular `Ψ_λ(y) = y`
implies that `Γ_λ(y,·)` is a regular relaxed equilibrium. -/
theorem corollary_2_1 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (hS : Standing U p) (hM : MeasMaps f p) (h21 : Assumption21 U f δ) (lam : ℝ) (hlam : 0 < lam)
    (y : Fin d → ℝ) :
    ((∃ pol : Control d ℓ, IsRegularRelaxedEq U p f δ lam pol ∧ y = Vlam U p f δ lam pol) ↔
        PsiLam U p f δ lam y = y) ∧
      (PsiLam U p f δ lam y = y → IsRegularRelaxedEq U p f δ lam (gibbsCtrl U f p lam y)) := by sorry
end RelaxedEqMDP.Discrete
