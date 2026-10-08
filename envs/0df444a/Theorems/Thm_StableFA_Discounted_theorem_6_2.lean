-- Prove2me | Theorems.Thm_StableFA_Discounted_theorem_6_2
-- name    : StableFA.Discounted.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:40:53.52298+00:00
-- url     : https://prove2.me/theorems/7ac740ce-84cf-4a9f-8f4b-9744f6a822c9
-- title:
--   Theorem 6.2, p. 12 — iteration of T_M ∘ M_A converges to V₀ with ‖V₀ − V*‖ ≤ 2γε/(1 − γ)
-- statement:
--   Let $M$ be a finite Markov decision process on states $1,\dots,n$ with nonempty finite action sets $U(i)$, expected costs $c_{ia}$, stochastic transition probabilities $p_{aij}$ and discount factor $0\le\gamma<1$. Let $T_M$ be its parallel value backup operator,
--   $$(T_MV)(i)=\min_{a\in U(i)}\Big(c_{ia}+\gamma\sum_j p_{aij}V(j)\Big),$$
--   and let $V^*$ be the optimal value function, i.e. the fixed point $T_MV^*=V^*$. Let $A$ be an averager with mapping $M_A$, let $V^A$ be any fixed point of $M_A$, and put $\varepsilon=\|V^A-V^*\|$, where $\|\cdot\|$ is the max norm. Then there is a value function $V_0$ such that, from every initial guess $V$, the iterates $(T_M\circ M_A)^k(V)$ converge to $V_0$, and
--   $$\|V_0-V^*\|\le\frac{2\gamma\varepsilon}{1-\gamma}.$$
--
--   So if the averager can represent some function within $\varepsilon$ of the optimal value function, approximate value iteration through it converges, from any start, to a value function whose error is of order $\varepsilon$; as $\gamma\to0$ the bound vanishes. Here $V_0$ denotes the *limit* of the iteration, not its starting point.
--
--   **Formalization Note** $V^*$ is taken as a hypothesis, the fixed point of $T_M$. This is licensed by the last clause of Theorem 2.2 (p. 4: "The fixed point of each of these operators is the optimal value function for the MDP"), which is the content of the published, proved theorem `BertsekasDP.discounted_main_theorem` (existence, uniqueness and optimality of the fixed point for $0<\gamma<1$; for $\gamma=0$ the fixed point is $\min_a c_{ia}$, plainly optimal). The page says "with discount factor $\gamma$"; the theorem sits in the paper's discounted discussion (§6.1: "If we are trying to solve a discounted MDP") and its proof uses that $T_M$ is a $\gamma$-contraction, so $\gamma<1$ is assumed. The MDP is `BertsekasSSPModel` plus the stochastic-row hypothesis; action sets may depend on the state, which harmlessly generalizes the paper's single action set. The averager acts on whole value functions (`Fin n → ℝ`), the sampled approximator being the special case of zero weights outside the sample. The iterated map is $T_M\circ M_A$ (fit, then back up), as on the page. $\|\cdot\|$ on `Fin n → ℝ` is the max norm.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 12, Theorem 6.2; proof pp. 12–13

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology

namespace StableFA.Discounted

theorem theorem_6_2 {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (A : Averager n) (Vstar VA : Fin n → ℝ) (ε : ℝ)
    (hV : BertsekasDiscountedBellmanOp M γ Vstar = Vstar)
    (hVA : A.apply VA = VA) (hε : ‖VA - Vstar‖ = ε) :
    ∃ V₀ : Fin n → ℝ,
      (∀ V : Fin n → ℝ,
        Tendsto (fun k => (BertsekasDiscountedBellmanOp M γ ∘ A.apply)^[k] V) atTop (𝓝 V₀)) ∧
      ‖V₀ - Vstar‖ ≤ 2 * γ * ε / (1 - γ) := by sorry

end StableFA.Discounted
