-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_proposition_2_2
-- name    : RelaxedEqMDP.Discrete.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:44.908554+00:00
-- url     : https://prove2.me/theorems/176d2cb6-ef5a-4b5e-80c5-c7dfee39906b
-- title:
--   Proposition 2.2, p. 9 — $\pi$ is a relaxed equilibrium iff $\pi\in\Phi(\pi)$; $y=V^\pi$ for one iff $y\in\Psi(y)$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumption 2.1 hold, and let $u\mapsto f(t,i,u)$ and $u\mapsto p^u_i$ be continuous on $U$. Then:
--   1. for every $\pi\in\Pi$, $$\pi\ \text{is a relaxed equilibrium for (2.1)}\iff\pi\in\Phi(\pi)=\Gamma(V^\pi);\qquad(2.24)$$
--   2. for every $y\in\mathbb R^d$, $y=V^\pi$ for some relaxed equilibrium $\pi\in\Pi$ if and only if $y\in\Psi(y)$.
--
--   Here $\Gamma(y)$ collects the relaxed controls with $\pi(i)$ supported in the argmax set $E(y,i)$ of $u\mapsto f(0,i,u)+p^u_i\cdot y$, and $\Psi(y)=\{V^\pi:\pi\in\Gamma(y)\}$. The proposition characterizes relaxed equilibria of the unregularized problem as fixed points of set-valued maps; Theorem 2.2 produces one as a limit.
--
--   **Formalization Note** "$\operatorname{supp}\pi(i)\subseteq E(y,i)$" is encoded as $\pi(i)(E(y,i)^c)=0$, equivalent here because $E(y,i)$ is closed.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 9, Proposition 2.2, (2.24)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Proposition 2.2, p. 9: under Assumption 2.1, with `u ↦ f(t,i,u)` and `u ↦ p^u_i` continuous,
`π ∈ Π` is a relaxed equilibrium iff `π ∈ Φ(π)` (2.24); moreover, for any `y ∈ ℝ^d`,
`y = V^π` for some relaxed equilibrium `π` iff `y ∈ Ψ(y)`. -/
theorem proposition_2_2 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (hS : Standing U p) (h21 : Assumption21 U f δ)
    (hfc : ∀ t i, ContinuousOn (f t i) U) (hpc : ∀ i j, ContinuousOn (fun u => p u i j) U) :
    (∀ pol : Control d ℓ, IsRelaxed U pol → (IsRelaxedEq U p f pol ↔ pol ∈ PhiSet U p f pol)) ∧
      ∀ y : Fin d → ℝ,
        (∃ pol : Control d ℓ, IsRelaxedEq U p f pol ∧ y = V p f pol) ↔ y ∈ PsiSet U p f y := by sorry
end RelaxedEqMDP.Discrete
