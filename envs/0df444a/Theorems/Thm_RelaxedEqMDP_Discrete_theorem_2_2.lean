-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_theorem_2_2
-- name    : RelaxedEqMDP.Discrete.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:51.935799+00:00
-- url     : https://prove2.me/theorems/50dd09fc-bc4e-4e79-825c-09b32b1569fe
-- title:
--   Theorem 2.2, p. 9 — under Assumptions 2.1–2.3 a relaxed equilibrium for the time-inconsistent MDP (2.1) exists
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.1, 2.2 and 2.3 hold. Then there is a relaxed feedback control $\pi\in\Pi$ that is a relaxed equilibrium for (2.1):
--   $$J^{\pi'\otimes_1\pi}(i)-J^\pi(i)\le0\qquad\text{for all } i\in\mathcal S\text{ and all }\pi'\in\Pi.$$
--
--   No convexity of $U$ and no concavity of the reward in the action is assumed: randomized (relaxed) controls replace them. Deviations $\pi'$ range over all relaxed controls, Dirac (deterministic) ones included.
--
--   **Formalization Note** The discount $\delta$ enters only through Assumption 2.1, as on the page (the theorem assumes it; it is the discount of the regularized problems used in the proof). Dropping it would give an equivalent statement, since $\delta(t)=2^{-t}$ always qualifies. Added hypotheses are those of the Setting: each $p^u$ is stochastic, $\Theta>0$, and Assumption 2.3 uses a one-nappe cone and an open ball (weaker than the printed double cone).
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 9, Theorem 2.2

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Theorem 2.2, p. 9: under Assumptions 2.1, 2.2 and 2.3, a relaxed equilibrium for (2.1) exists. -/
theorem theorem_2_2 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta) :
    ∃ pol : Control d ℓ, IsRelaxedEq U p f pol := by sorry
end RelaxedEqMDP.Discrete
