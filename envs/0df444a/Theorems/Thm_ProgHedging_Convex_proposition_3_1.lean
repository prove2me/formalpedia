-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_3_1
-- name    : ProgHedging.Convex.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:00.989865+00:00
-- url     : https://prove2.me/theorems/2e152801-9e14-4cb8-be5b-489adeb652f3
-- title:
--   Proposition 3.1 — each (P_s) attains its minimum, α̂ = min over 𝒞 of F is attained, equals E{α_s}, and bounds min (P) below
-- statement:
--   Under the standing assumptions, each scenario subproblem $(P_s)$ — minimize $f_s$ over $C_s$ — has an optimal solution, hence a finite optimal value $\alpha_s=\min(P_s)$. Moreover the value
--
--   $$
--   \hat\alpha=\min_{X\in\mathcal C}F(X)
--   $$
--
--   is attained, and for any choice of optimal solutions $x_s$ of $(P_s)$,
--
--   $$
--   \hat\alpha=E\{\alpha_s\}=\sum_{s\in S}p_s f_s(x_s).
--   $$
--
--   Finally $\hat\alpha\le\min(P)$, the optimal value of (P) (which is $+\infty$ if (P) is infeasible).
--
--   This identifies the trivial lower bound obtained by solving the scenarios separately, the starting point $X^0$ suggested for the algorithm.
--
--   **Formalization Note.** $\hat\alpha$ is the `EReal` infimum of $F$ over $\mathcal C$; its attainment is part of the statement. $\alpha_s$ is written as $f_s(x_s)$ for an arbitrary family of minimizers.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 10–11, Proposition 3.1, (3.2)–(3.3)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 3.1, pp. 10–11. Each scenario subproblem `(P_s)` attains its minimum; the value
`α̂ = min_{X ∈ 𝒞} F(X)` is attained and equals `E{α_s}` with `α_s = min (P_s)`; and `α̂ ≤ min (P)`. -/
theorem proposition_3_1 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    (∀ s, ∃ x ∈ pr.C s, ∀ z ∈ pr.C s, pr.f s x ≤ pr.f s z) ∧
    (∃ X ∈ pr.adm, ((pr.F X : ℝ) : EReal) = pr.alphaHat) ∧
    (∀ xs : S → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ pr.C s ∧ ∀ z ∈ pr.C s, pr.f s (xs s) ≤ pr.f s z) →
        pr.alphaHat = ((∑ s, pr.p s * pr.f s (xs s) : ℝ) : EReal)) ∧
    pr.alphaHat ≤ pr.minP := by sorry

end ProgHedging.Convex
