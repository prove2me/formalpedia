-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_theorem_2_1
-- name    : RelaxedEqMDP.Discrete.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:59.798265+00:00
-- url     : https://prove2.me/theorems/98dd86e5-332d-4d58-ae7c-574b447c2c8a
-- title:
--   Theorem 2.1, p. 8 — for every $\lambda>0$ a regular relaxed equilibrium exists, as a fixed point of $\Psi_\lambda$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.1, 2.2 and 2.3 hold. For every $\lambda>0$ there is $y\in\mathbb R^d$ with
--   $$\Psi_\lambda(y)=y,$$
--   and then $\Gamma_\lambda(y,\cdot)\in\Pi_r$ is a regular relaxed equilibrium for the entropy-regularized problem (2.4).
--
--   This is the existence result for the regularized problem; Theorem 2.2 obtains the unregularized result as $\lambda\downarrow0$.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 8, Theorem 2.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Theorem 2.1, p. 8: under Assumptions 2.1–2.3, for any `λ > 0` there is `y ∈ ℝ^d` with
`Ψ_λ(y) = y`; hence `Γ_λ(y,·) ∈ Π_r` is a regular relaxed equilibrium for (2.4). -/
theorem theorem_2_1 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ y : Fin d → ℝ, PsiLam U p f δ lam y = y ∧
      IsRegularRelaxedEq U p f δ lam (gibbsCtrl U f p lam y) := by sorry
end RelaxedEqMDP.Discrete
