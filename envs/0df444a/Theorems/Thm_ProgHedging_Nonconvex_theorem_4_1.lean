-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_theorem_4_1
-- name    : ProgHedging.Nonconvex.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:28.526113+00:00
-- url     : https://prove2.me/theorems/7ffd29d1-2061-4149-9f0c-d005521686af
-- title:
--   Theorem 4.1 — Clarke optimality conditions for (P) under a constraint qualification, sufficient in the convex case
-- statement:
--   Let $X^*$ be a feasible solution of (P): $X^*\in\mathcal N$ and $X^*\in\mathcal C$, i.e. $X^*(s)\in C_s$ for all $s\in S$ (4.1).
--
--   1. Suppose $X^*$ is locally optimal for (P) and the **constraint qualification**
--   $$\text{the only } W\in\mathcal M \text{ with } -W(s)\in N_{C_s}(X^*(s)) \text{ for all } s\in S \text{ is } W=0 \tag{4.2}$$
--   holds. Then there exists $W^*\in\mathcal M$ with
--   $$-W^*(s)\in\partial f_s(X^*(s))+N_{C_s}(X^*(s))\qquad\text{for all } s\in S. \tag{4.4}$$
--   2. In the convex case, if some $W^*\in\mathcal M$ satisfies (4.4), then $X^*$ is a globally optimal solution of (P): $F(X^*)\le F(X)$ for all $X\in\mathcal C\cap\mathcal N$.
--
--   Here $\partial$ is Clarke's generalized gradient and $N_{C}$ Clarke's normal cone. The theorem identifies the price systems $W^*$ of progressive hedging as Lagrange multipliers for the nonanticipativity constraint, and it is the yardstick for the limits of the algorithm in Theorem 6.1.
--
--   **Formalization Note** The paper states the conclusion as (4.3), $-W^*\in\partial F(X^*)+N_{\mathcal C}(X^*)$ on $\mathcal E$ with the inner product $\langle\cdot,\cdot\rangle$, and asserts that it is equivalent to (4.4); only the decomposed form (4.4) is formalized, so no Clarke calculus on $\mathcal E$ is needed. "Locally optimal" means $F(X^*)\le F(X)$ for all feasible $X$ in some neighbourhood of $X^*$ (the choice of norm on $\mathcal E$ does not matter in finite dimension).
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 14–15, Theorem 4.1

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open scoped Pointwise

namespace ProgHedging.Nonconvex

/-- Theorem 4.1, pp. 14–15: at a locally optimal feasible `X*` of (P) satisfying the constraint
qualification (4.2) there is `W* ∈ ℳ` with (4.4); in the convex case any `W*` with the optimality
conditions (4.1), (4.4), `W* ∈ ℳ`, makes `X*` globally optimal for (P). -/
theorem theorem_4_1 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (Xs : ProgHedging.Convex.Policy S n)
    (hXN : Xs ∈ pr.N) (hXC : Xs ∈ pr.adm) :
    ((∃ ε > 0, ∀ Y ∈ pr.adm ∩ pr.N, dist Y Xs < ε → pr.F Xs ≤ pr.F Y) →
      (∀ W ∈ pr.M, (∀ s, -W s ∈ ClarkeGradients.FlowInvariance.normalCone (pr.C s) (Xs s)) →
        W = 0) →
      ∃ Ws ∈ pr.M, ∀ s, -Ws s ∈ ClarkeGradients.Shared.generalizedGradient (pr.f s) (Xs s) +
        ClarkeGradients.FlowInvariance.normalCone (pr.C s) (Xs s)) ∧
    (pr.ConvexCase → ∀ Ws : ProgHedging.Convex.Policy S n, pr.OptCond41 Xs Ws →
      ∀ Y ∈ pr.adm ∩ pr.N, pr.F Xs ≤ pr.F Y) := by sorry

end ProgHedging.Nonconvex
