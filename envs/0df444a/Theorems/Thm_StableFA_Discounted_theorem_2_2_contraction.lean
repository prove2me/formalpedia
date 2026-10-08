-- Prove2me | Theorems.Thm_StableFA_Discounted_theorem_2_2_contraction
-- name    : StableFA.Discounted.theorem_2_2_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:39:53.640094+00:00
-- url     : https://prove2.me/theorems/5581d6c4-b17c-42e4-b526-84cdf514cdd3
-- title:
--   Theorem 2.2, first clause, p. 4 — the discounted parallel value backup is a γ-contraction in max norm
-- statement:
--   Let $M$ be a finite Markov decision process with states $1,\dots,n$, admissible action sets $U(i)$ (finite and nonempty), expected one-step costs $c_{ia}$ and transition probabilities $p_{aij}\ge 0$ with $\sum_j p_{aij}=1$ for every admissible action $a\in U(i)$. Let $0\le\gamma<1$ be the discount factor. The parallel value iteration operator $T_M$ maps a value function $V\in\mathbb R^n$ to
--   $$(T_M V)(i)=\min_{a\in U(i)}\Big(c_{ia}+\gamma\sum_{j=1}^n p_{aij}V(j)\Big).$$
--   Then $T_M$ is a contraction in the max norm $\|V\|=\max_i|V(i)|$ with contraction factor $\gamma$: for all $V,W\in\mathbb R^n$,
--   $$\|T_M V-T_M W\|\le\gamma\,\|V-W\| .$$
--
--   This is the basic fact behind the convergence of value iteration in discounted problems, and the starting point of every stability and error bound for approximate value iteration in this mission.
--
--   **Formalization Note** The MDP is the published `BertsekasSSPModel`, whose rows are only substochastic; the hypothesis $\sum_j p_{aij}=1$ makes it Gordon's (stochastic) MDP. $\|\cdot\|$ on `Fin n → ℝ` is the max norm. Action sets may differ between states, which harmlessly generalizes the paper's single action set $A$. This item is the first sentence of Theorem 2.2 only; the nondiscounted clause and the identification of the fixed point with the optimal value function are not part of it.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 4, Theorem 2.2 (value contraction), first sentence

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology

namespace StableFA.Discounted

theorem theorem_2_2_contraction {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1) :
    ∀ V W : Fin n → ℝ,
      ‖BertsekasDiscountedBellmanOp M γ V - BertsekasDiscountedBellmanOp M γ W‖ ≤
        γ * ‖V - W‖ := by sorry

end StableFA.Discounted
