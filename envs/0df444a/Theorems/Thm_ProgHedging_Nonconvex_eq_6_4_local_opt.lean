-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_eq_6_4_local_opt
-- name    : ProgHedging.Nonconvex.eq_6_4_local_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:59.983997+00:00
-- url     : https://prove2.me/theorems/0aaa613f-9623-4918-a68d-9f5f70842277
-- title:
--   (6.4)–(6.5) — each δ-locally optimal step X^{ν+1} is δ′-locally optimal for (P^ν), δ′ = δ min p_s^{1/2}
-- statement:
--   Let $r>0$, $\delta>0$, and let $(X^\nu)$, $(W^\nu)$ be a run of progressive hedging in which each $X^{\nu+1}(s)$ is $\delta$-locally optimal for the scenario subproblem $(P^\nu_s)$. Put $\delta'=\delta\min_{s}p_s^{1/2}$ and let $F^\nu(X)=F(X)+\langle X,W^\nu\rangle+\tfrac12 r\|X-\hat X^\nu\|^2$ with $\hat X^\nu=JX^\nu$. Then:
--
--   1. for all policies $X,Z$, $\|X-Z\|\le\delta'$ implies $|X(s)-Z(s)|\le\delta$ for every $s\in S$ (6.5);
--   2. for every $\nu$, $X^{\nu+1}\in\mathcal C$ and
--   $$F^\nu(X^{\nu+1})\le F^\nu(X)\qquad\text{for all } X\in\mathcal C \text{ with } \|X-X^{\nu+1}\|\le\delta'.$$
--
--   The per-scenario local optimality thus transfers to the aggregated subproblem $(P^\nu)$ with a uniform radius in the norm of $\mathcal E$; this is the first step towards passing to the limit.
--
--   **Formalization Note** $\|\cdot\|$ is the weighted norm $\langle X,X\rangle^{1/2}$ (`pnorm`), and $|\cdot|$ the Euclidean norm of $\mathbb R^n$.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 31, proof of Theorem 6.1, (6.3)–(6.5)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open scoped RealInnerProductSpace

namespace ProgHedging.Nonconvex

/-- Proof of Theorem 6.1, p. 31, (6.4)–(6.5): a weighted-norm ball of radius
`δ′ = δ min_s p_s^{1/2}` lies inside the product of the Euclidean `δ`-balls (6.5), and hence each
`X^{ν+1}` is `δ′`-locally optimal in `(P^ν)`: minimize `F^ν` (6.3) over `𝒞`. -/
theorem eq_6_4_local_opt {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W) :
    (∀ Y Z : ProgHedging.Convex.Policy S n, pr.pnorm (Y - Z) ≤ pr.deltaPrime δ → ∀ s, ‖Y s - Z s‖ ≤ δ) ∧
    ∀ ν, X (ν + 1) ∈ pr.adm ∧ ∀ Y ∈ pr.adm, pr.pnorm (Y - X (ν + 1)) ≤ pr.deltaPrime δ →
      pr.Fnu r (pr.J (X ν)) (W ν) (X (ν + 1)) ≤ pr.Fnu r (pr.J (X ν)) (W ν) Y := by sorry

end ProgHedging.Nonconvex
