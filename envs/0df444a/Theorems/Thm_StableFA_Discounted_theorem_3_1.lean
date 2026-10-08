-- Prove2me | Theorems.Thm_StableFA_Discounted_theorem_3_1
-- name    : StableFA.Discounted.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:40:19.595258+00:00
-- url     : https://prove2.me/theorems/279ab6a4-b940-461b-a4ae-526018da11d3
-- title:
--   Theorem 3.1, p. 5 — a max-norm nonexpansion M_F is compatible with T_M, and M_F ∘ T_M has contraction factor γ
-- statement:
--   Let $M$ be a finite MDP on $n$ states with stochastic transition rows and discount factor $0\le\gamma<1$, and let $T_M$ be its parallel value backup operator,
--   $$(T_M V)(i)=\min_{a\in U(i)}\Big(c_{ia}+\gamma\sum_{j}p_{aij}V(j)\Big).$$
--   Let $M_F:\mathbb R^n\to\mathbb R^n$ be the mapping of a function approximator, and suppose $M_F$ is a nonexpansion in max norm, $\|M_F(Y)-M_F(Z)\|\le\|Y-Z\|$ for all $Y,Z$. Then
--
--   1. $M_F$ is compatible with $T_M$: for every initial guess $V_0$ the iterates $(M_F\circ T_M)^k(V_0)$ converge; and
--   2. $M_F\circ T_M$ has contraction factor $\gamma$: for all $V,W\in\mathbb R^n$,
--   $$\|M_F(T_MV)-M_F(T_MW)\|\le\gamma\,\|V-W\| .$$
--
--   Approximate value iteration alternates a backup with a fit; this theorem says that any fit that does not expand max-norm distances keeps the combined iteration a contraction.
--
--   **Formalization Note** $M_F$ is an arbitrary map on value functions `Fin n → ℝ` (not necessarily an averager). The page writes "Let $X=S\times A$" and $M_F\in\mathbb R^{|X|}\mapsto\mathbb R^{|X|}$; since $T_M$ is the parallel *value* backup and acts on functions of the state, the composition only makes sense on value functions over the states, which is how it is stated here. $\|\cdot\|$ on `Fin n → ℝ` is the max norm.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 5, Theorem 3.1; proof p. 6

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology

namespace StableFA.Discounted

theorem theorem_3_1 {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (MF : (Fin n → ℝ) → (Fin n → ℝ)) (hMF : ∀ Y Z : Fin n → ℝ, ‖MF Y - MF Z‖ ≤ ‖Y - Z‖) :
    Compatible MF (BertsekasDiscountedBellmanOp M γ) ∧
    ∀ V W : Fin n → ℝ,
      ‖MF (BertsekasDiscountedBellmanOp M γ V) - MF (BertsekasDiscountedBellmanOp M γ W)‖ ≤
        γ * ‖V - W‖ := by sorry

end StableFA.Discounted
