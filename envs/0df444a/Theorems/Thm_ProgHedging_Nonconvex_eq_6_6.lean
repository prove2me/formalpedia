-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_eq_6_6
-- name    : ProgHedging.Nonconvex.eq_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:09.192989+00:00
-- url     : https://prove2.me/theorems/57204bf9-c491-4119-8eda-73025f8a011e
-- title:
--   (6.6) — in the limit X* is δ′-locally optimal for (P*): minimize F(X) + ⟨X, W*⟩ + ½r‖X − X*‖² over 𝒞
-- statement:
--   Let $r>0$, $\delta>0$, and let $(X^\nu)$, $(W^\nu)$ be a run of progressive hedging with $\delta$-locally optimal subproblem solutions, with $X^\nu\to X^*$ and $W^\nu\to W^*$. Let $\delta'=\delta\min_s p_s^{1/2}$. Then $X^*\in\mathcal C$ and
--   $$F(X)+\langle X,W^*\rangle+\tfrac12 r\|X-X^*\|^2\ \ge\ F(X^*)+\langle X^*,W^*\rangle\qquad\text{for all } X\in\mathcal C \text{ with } \|X-X^*\|<\delta' .$$
--   In other words $X^*$ is locally optimal for the problem
--   $$(P^*)\qquad \text{minimize } F(X)+\langle X,W^*\rangle+\tfrac12 r\|X-X^*\|^2 \text{ over } X\in\mathcal C .$$
--
--   This is the limit form of the local optimality of the iterates, and the step from which both conclusions of Theorem 6.1 are drawn.
--
--   **Formalization Note** The paper writes the neighbourhood as $\|X-X^*\|\le\delta'$. With the closed ball the inequality can fail: a point of $\mathcal C$ at distance exactly $\delta'$ from $X^*$ may lie outside every closed $\delta'$-ball around $X^{\nu+1}$ (e.g. one scenario, $C=\{0,1\}\cup\{-\rho^k\}$, iterates $-\rho^\nu\to0$, $\delta=1$, and a very low cost at $1$). The statement therefore uses the open ball, which is what the limiting argument gives and all that "locally optimal" requires. On the left the paper prints $\tfrac12 r\|X-X'\|^2$; this is read as $\|X-X^*\|^2$, as the definition of $(P^*)$ shows, and the right-hand term $\tfrac12 r\|X^*-X^*\|^2=0$ is omitted. $\|\cdot\|$ is the weighted norm (`pnorm`).
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 31, proof of Theorem 6.1, (6.6) and (P*)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open Filter Topology

namespace ProgHedging.Nonconvex

/-- (6.6), p. 31: in the limit, `X*` is admissible and `δ′`-locally optimal (relative to the open
`δ′`-ball of the norm (2.3)) for `(P*)`: minimize `F(X) + ⟨X, W*⟩ + ½r‖X − X*‖²` over `𝒞`. -/
theorem eq_6_6 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    Xs ∈ pr.adm ∧ ∀ Y ∈ pr.adm, pr.pnorm (Y - Xs) < pr.deltaPrime δ →
      pr.F Xs + pr.ip Xs Ws ≤ pr.F Y + pr.ip Y Ws + r / 2 * pr.pnorm (Y - Xs) ^ 2 := by sorry

end ProgHedging.Nonconvex
