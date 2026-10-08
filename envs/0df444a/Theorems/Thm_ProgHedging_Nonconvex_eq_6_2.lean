-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_eq_6_2
-- name    : ProgHedging.Nonconvex.eq_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:17.639171+00:00
-- url     : https://prove2.me/theorems/d7f73c6e-c683-4d20-af76-1928dae0fca1
-- title:
--   (6.2) — the proximal term does not change the generalized gradient at X*(s): ∂f̃_s(X*(s)) = ∂f_s(X*(s))
-- statement:
--   Let $r\in\mathbb R$, let $X^*$ be a policy and $s\in S$, and let $\tilde f_s(x)=f_s(x)+\tfrac12 r|x-X^*(s)|^2$. Writing $\partial$ for Clarke's generalized gradient,
--
--   1. for every $x\in\mathbb R^n$,
--   $$\partial\tilde f_s(x)=\partial f_s(x)+r\,(x-X^*(s));$$
--   2. consequently
--   $$\partial\tilde f_s(X^*(s))=\partial f_s(X^*(s)) .\tag{6.2}$$
--
--   Because of (6.2), the optimality conditions of Theorem 4.1 for the modified problem $(\tilde P)$ and for the original problem (P) coincide at $X^*$; this is how the paper turns the multiplier statement for $(\tilde P)$ into stationarity for (P).
--
--   **Formalization Note** The first identity is the sum rule for the generalized gradient of a locally Lipschitz function plus a smooth function, which the paper cites from Clarke's book (Corollary 2.4.2 of [7] as printed). It is stated for every real $r$; the paper's $r$ is positive. The paper prints $\partial\hat f_s$ on the left of (6.2); it means $\partial\tilde f_s$.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 30–31, proof of Theorem 6.1, display before (6.2) and (6.2)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open scoped Pointwise

namespace ProgHedging.Nonconvex

/-- Proof of Theorem 6.1, pp. 30–31, and (6.2): `∂f̃_s(x) = ∂f_s(x) + r(x − X*(s))` for every `x`,
and consequently `∂f̃_s(X*(s)) = ∂f_s(X*(s))` (Clarke generalized gradients). -/
theorem eq_6_2 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (Xs : ProgHedging.Convex.Policy S n) (s : S) :
    (∀ x : EuclideanSpace ℝ (Fin n),
      ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) x =
        ClarkeGradients.Shared.generalizedGradient (pr.f s) x + {r • (x - Xs s)}) ∧
    ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) (Xs s) =
      ClarkeGradients.Shared.generalizedGradient (pr.f s) (Xs s) := by sorry

end ProgHedging.Nonconvex
