-- Prove2me | Theorems.Thm_StableFA_DerivedMDP_theorem_4_1
-- name    : StableFA.DerivedMDP.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:16.077199+00:00
-- url     : https://prove2.me/theorems/436228fd-5c31-4ed3-addc-ff3a12de822b
-- title:
--   Theorem 4.1 (Derived MDP), p. 7 — T_M ∘ M_A is the parallel value backup operator of the derived MDP M′
-- statement:
--   Let $M$ be a finite Markov decision process with cost-free absorbing goal state $1$ and discount factor $\gamma$, whose parallel value backup operator is
--   $$(T_M V)(x)=\min_{a}\Bigl[c_{xa}+\gamma\sum_y p_{axy}V(y)\Bigr]\qquad(V(1)=0),$$
--   and let $A$ be an averager with mapping $M_A(V)(y)=\beta_yk_y+\sum_z\beta_{yz}V(z)$. Let $M'$ be the derived MDP with the same states, actions and discount, transition probabilities $p'_{axz}=\sum_y p_{axy}\beta_{yz}$ ($z\ne 1$) and expected costs $c'_{xa}=c_{xa}+\gamma\sum_{y'}p_{axy'}\beta_{y'}k_{y'}$. Then
--   $$T_{M'}=T_M\circ M_A .$$
--   This holds for the discounted backup with every discount factor $\gamma$, and for the nondiscounted backup ($\gamma=1$).
--
--   This is the central observation of the report: approximate value iteration with an averager is exact value iteration on another Markov decision process, so its convergence is a question about $M'$.
--
--   **Formalization Note** The new process $M'$ is the explicit `derivedModel M A γ` of the definitions file. The identity is algebraic and is stated for every real $\gamma$; the paper's discount factors are special cases. The first conjunct uses `BertsekasDiscountedBellmanOp`, the second the nondiscounted `BertsekasSSPBellmanOp` with the model `derivedModel M A 1`. The goal is the implicit termination state, so no hypothesis $V(1)=0$ is needed (the page's final display uses it silently).
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 7, Theorem 4.1 (Derived MDP); proof pp. 9–10

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem theorem_4_1 {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n) :
    (∀ γ : ℝ, BertsekasDiscountedBellmanOp (derivedModel M A γ) γ =
        BertsekasDiscountedBellmanOp M γ ∘ A.apply) ∧
      BertsekasSSPBellmanOp (derivedModel M A 1) = BertsekasSSPBellmanOp M ∘ A.apply := by sorry

end StableFA.DerivedMDP
