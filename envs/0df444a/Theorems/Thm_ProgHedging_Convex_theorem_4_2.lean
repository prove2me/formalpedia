-- Prove2me | Theorems.Thm_ProgHedging_Convex_theorem_4_2
-- name    : ProgHedging.Convex.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:12.598645+00:00
-- url     : https://prove2.me/theorems/620957b0-23ef-4684-90c0-c57fe888433a
-- title:
--   Theorem 4.2 — in the convex case the optimality conditions (4.1), (4.4) are equivalent to a saddle point of the Lagrangian
-- statement:
--   Assume the convex case. For a pair $(X^*,W^*)\in\mathcal N\times\mathcal M$ the following are equivalent:
--
--   1. the decomposed optimality conditions: for every scenario $s$, $X^*(s)\in C_s$ and
--   $$
--   -W^*(s)\in\partial f_s(X^*(s))+N_{C_s}(X^*(s));
--   $$
--   2. $(X^*,W^*)$ is a saddle point of the Lagrangian $L(X,W)=F(X)+\langle X,W\rangle$ relative to minimizing over $X\in\mathcal C$ and maximizing over $W\in\mathcal M$.
--
--   Here $\partial f_s$ is the subgradient set of convex analysis and $N_{C_s}$ the normal cone of convex analysis. The theorem identifies the multipliers $W^*$ of the scenario-wise conditions with Lagrange multipliers for the implementability constraint.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 17, Theorem 4.2, with (4.1), (4.4) on pp. 14–15

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Theorem 4.2, p. 17. In the convex case, for `(X*, W*) ∈ 𝒩 × ℳ` the decomposed conditions
(4.1) and (4.4) hold iff `(X*, W*)` is a saddle point of `L(X, W) = F(X) + ⟨X, W⟩` relative to
minimizing over `X ∈ 𝒞` and maximizing over `W ∈ ℳ`. -/
theorem theorem_4_2 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) (Xs Ws : Policy S n) (hXs : Xs ∈ pr.N) (hWs : Ws ∈ pr.M) :
    pr.OptCond Xs Ws ↔ pr.IsSaddle Xs Ws := by sorry

end ProgHedging.Convex
