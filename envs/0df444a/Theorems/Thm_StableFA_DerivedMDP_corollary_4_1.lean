-- Prove2me | Theorems.Thm_StableFA_DerivedMDP_corollary_4_1
-- name    : StableFA.DerivedMDP.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:18.855857+00:00
-- url     : https://prove2.me/theorems/975c844b-09f3-413e-b4d2-f343025fadd6
-- title:
--   Corollary 4.1, p. 11 — all policies proper and A self-weighted ⇒ T_M and M_A are compatible and approximate value iteration converges
-- statement:
--   Let $M$ be a finite nondiscounted Markov decision process with a cost-free absorbing goal state, in which every policy is proper. Let $A$ be an averager that is self-weighted for $M$, let $T_M$ be the parallel value backup operator of $M$ (which sets $V(1)=0$) and $M_A$ the mapping of $A$. Then:
--
--   1. $T_M$ and $M_A$ are compatible: for every initial guess $V_0$ the iterates $(M_A\circ T_M)^k(V_0)$ converge;
--   2. approximate value iteration based on $A$ converges when applied to $M$: for every initial guess $V_0$ the iterates $(T_M\circ M_A)^k(V_0)$ converge.
--
--   This is the report's convergence guarantee for nondiscounted problems. An averager need not be a nonexpansion in the weighted max norm in which $T_M$ contracts, and approximate value iteration can diverge (Figure 4); self-weighting rules that out.
--
--   **Formalization Note** "Compatible" follows the definition on p. 5: `Compatible MF T` iterates `MF ∘ T`, so part 1 is `Compatible A.apply (BertsekasSSPBellmanOp M)`. The approximate value iteration sequence of p. 10 interleaves the two orders, $V_0, M_A(V_0), T_M(M_A(V_0)),\dots$; part 2 states the convergence of $T_M\circ M_A$, the other order. The goal is the implicit termination state of `BertsekasSSPModel`; its value is $0$. "All policies proper" quantifies over stationary policies (p. 3). The hypotheses are about $M$ and $A$ only; nothing is assumed about the derived MDP.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 11, Corollary 4.1; argument pp. 9–10

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem corollary_4_1 {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    StableFA.Discounted.Compatible A.apply (BertsekasSSPBellmanOp M) ∧
      StableFA.Discounted.Compatible (BertsekasSSPBellmanOp M) A.apply := by sorry

end StableFA.DerivedMDP
