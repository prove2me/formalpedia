-- Prove2me | Theorems.Thm_StableFA_Discounted_theorem_3_2
-- name    : StableFA.Discounted.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:40:04.021834+00:00
-- url     : https://prove2.me/theorems/3ecd5fd3-5047-47a4-9aaf-45e5e25232f4
-- title:
--   Theorem 3.2, p. 7 — the mapping of an averager is a max-norm nonexpansion, hence compatible with discounted value backups
-- statement:
--   Let $A$ be an averager on $n$ states, with constants $k_i$ and nonnegative weights $\beta_i,\beta_{ij}$ satisfying $\beta_i+\sum_j\beta_{ij}=1$, and let $M_A(Y)_i=\beta_ik_i+\sum_j\beta_{ij}Y_j$ be its mapping. Then:
--
--   1. $M_A$ is a nonexpansion in the max norm: for all $Y,Z\in\mathbb R^n$,
--   $$\|M_A(Y)-M_A(Z)\|\le\|Y-Z\| ;$$
--   2. $M_A$ is compatible with the parallel value backup operator $T_M$ of every discounted finite MDP $M$ on the same $n$ states (discount $0\le\gamma<1$, stochastic transition rows): for every initial guess $V_0$ the iterates $(M_A\circ T_M)^k(V_0)$ converge.
--
--   The theorem singles out the averagers as a class of function approximators that cannot exaggerate differences between target value functions, and therefore can be combined with value iteration without risking divergence.
--
--   **Formalization Note** $\|\cdot\|$ on `Fin n → ℝ` is the max norm. The MDP is `BertsekasSSPModel` with the stochastic-row hypothesis, any finite action type and any nonempty admissible action sets. The second part is stated for every such MDP, as on the page ("for any discounted MDP").
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 7, Theorem 3.2

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology

namespace StableFA.Discounted

theorem theorem_3_2 {n : ℕ} (A : Averager n) :
    (∀ Y Z : Fin n → ℝ, ‖A.apply Y - A.apply Z‖ ≤ ‖Y - Z‖) ∧
    ∀ (C : Type) [Fintype C] (M : BertsekasSSPModel n C) (γ : ℝ), 0 ≤ γ → γ < 1 →
      (∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1) →
      Compatible A.apply (BertsekasDiscountedBellmanOp M γ) := by sorry

end StableFA.Discounted
