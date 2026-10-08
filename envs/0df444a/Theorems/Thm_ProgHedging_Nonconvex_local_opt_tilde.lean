-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_local_opt_tilde
-- name    : ProgHedging.Nonconvex.local_opt_tilde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:08.082987+00:00
-- url     : https://prove2.me/theorems/4550a30b-8edd-4a33-978b-15daeda3dd20
-- title:
--   Proof of Theorem 6.1 — X* is δ′-locally optimal for F(X) + ½r‖X − X*‖² = E{f̃_s(X(s))} over 𝒞 ∩ 𝒩
-- statement:
--   Let $r>0$, $\delta>0$, and let $(X^\nu)$, $(W^\nu)$ be a run of progressive hedging with $\delta$-locally optimal subproblem solutions, with $X^\nu\to X^*$ and $W^\nu\to W^*$. Let $\delta'=\delta\min_s p_s^{1/2}$ and $\tilde f_s(x)=f_s(x)+\tfrac12 r|x-X^*(s)|^2$. Then
--
--   1. $F(X^*)\le F(X)+\tfrac12 r\|X-X^*\|^2$ for all $X\in\mathcal C\cap\mathcal N$ with $\|X-X^*\|<\delta'$;
--   2. for every policy $X$,
--   $$F(X)+\tfrac12 r\|X-X^*\|^2=\sum_{s\in S}p_s\,\tilde f_s(X(s))=E\{\tilde f_s(X(s))\}.$$
--
--   Together these say that $X^*$ is a local minimizer of the modified problem $(\tilde P)$, in which each $f_s$ is replaced by $\tilde f_s$.
--
--   **Formalization Note** As in (6.6), the paper's closed ball $\|X-X^*\|\le\delta'$ is replaced by the open ball; see the note on (6.6) for why the closed-ball version can fail. $\|\cdot\|$ is the weighted norm (`pnorm`).
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 31, proof of Theorem 6.1, last paragraph

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open Filter Topology

namespace ProgHedging.Nonconvex

/-- Proof of Theorem 6.1, p. 31: `X*` is `δ′`-locally optimal (open `δ′`-ball of the norm (2.3))
for minimizing `F(X) + ½r‖X − X*‖² = E{f̃_s(X(s))}` over `𝒞 ∩ 𝒩`, and that identity holds. -/
theorem local_opt_tilde {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    (∀ Y ∈ pr.adm ∩ pr.N, pr.pnorm (Y - Xs) < pr.deltaPrime δ →
      pr.F Xs ≤ pr.F Y + r / 2 * pr.pnorm (Y - Xs) ^ 2) ∧
    ∀ Y : ProgHedging.Convex.Policy S n, pr.F Y + r / 2 * pr.pnorm (Y - Xs) ^ 2 = ∑ s, pr.p s * pr.fTilde r Xs s (Y s) := by sorry

end ProgHedging.Nonconvex
