-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_continuous_PsiLam
-- name    : RelaxedEqMDP.Discrete.continuous_PsiLam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:42.162216+00:00
-- url     : https://prove2.me/theorems/2e19dac3-d34f-4512-b6d5-21c22e1b4d03
-- title:
--   Proof of Theorem 2.1, pp. 20–21 — $\Psi_\lambda:\mathbb R^d\to\mathbb R^d$ is continuous
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.1, 2.2 and 2.3 hold and $\lambda>0$. Then the map
--   $$\Psi_\lambda:\mathbb R^d\to\mathbb R^d,\qquad \Psi_\lambda(y)=V^{\Gamma_\lambda(y,\cdot)}_\lambda,$$
--   is continuous.
--
--   Continuity is the first half of the Brouwer argument for Theorem 2.1.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, pp. 20–21, proof of Theorem 2.1 (Appendix A.2), first paragraph

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Proof of Theorem 2.1, pp. 20–21: under Assumptions 2.1–2.3, for `λ > 0` the map
`Ψ_λ : ℝ^d → ℝ^d` is continuous. -/
theorem continuous_PsiLam {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta)
    (lam : ℝ) (hlam : 0 < lam) :
    Continuous (PsiLam U p f δ lam) := by sorry
end RelaxedEqMDP.Discrete
