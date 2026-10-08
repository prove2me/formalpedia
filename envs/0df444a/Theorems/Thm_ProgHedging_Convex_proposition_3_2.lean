-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_3_2
-- name    : ProgHedging.Convex.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:29.170217+00:00
-- url     : https://prove2.me/theorems/37fb0d71-9fb9-4154-a9a9-c09ff57cfba5
-- title:
--   Proposition 3.2 — every modified scenario subproblem has an optimal solution, unique in the convex case
-- statement:
--   Let $s\in S$, $\hat x,w\in\mathbb R^n$ and $r>0$. The modified scenario subproblem
--
--   $$
--   (\hat P_s(\hat x,w,r))\qquad \text{minimize } f_s(x)+x\cdot w+\tfrac12 r\,|x-\hat x|^2 \text{ over } x\in C_s
--   $$
--
--   has at least one optimal solution (so a finite optimal value). In the convex case its optimal solution is unique.
--
--   The subproblems $(P^\nu_s)$ of the progressive hedging algorithm are of this form, so this is what makes Step 2 of the algorithm well defined.
--
--   **Formalization Note.** "Finite optimal value" is automatic for a real-valued objective with a minimizer, so it is not stated separately.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 11, Proposition 3.2, (3.4); (P̂_s(x̂, w, r)) defined p. 7

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem

open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 3.2, p. 11. For `r > 0`, every modified scenario subproblem
`(P̂_s(x̂, w, r))  minimize f_s(x) + x·w + ½ r |x − x̂|²  over x ∈ C_s`
has an optimal solution (hence a finite optimal value); in the convex case it is unique. -/
theorem proposition_3_2 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (s : S)
    (xhat w : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    (∃ x ∈ pr.C s, ∀ z ∈ pr.C s, pr.subObj s xhat w r x ≤ pr.subObj s xhat w r z) ∧
    (pr.ConvexCase → ∀ x ∈ pr.C s, ∀ x' ∈ pr.C s,
      (∀ z ∈ pr.C s, pr.subObj s xhat w r x ≤ pr.subObj s xhat w r z) →
      (∀ z ∈ pr.C s, pr.subObj s xhat w r x' ≤ pr.subObj s xhat w r z) → x = x') := by sorry

end ProgHedging.Convex
