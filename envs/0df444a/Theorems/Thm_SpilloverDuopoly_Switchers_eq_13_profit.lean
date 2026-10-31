-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_eq_13_profit
-- name    : SpilloverDuopoly.Switchers.eq_13_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:28.829073+00:00
-- url     : https://prove2.me/theorems/7393f367-46b4-4cc4-85b9-ecdc4daf5f7a
-- title:
--   Equation (13), p. 21 (PDF 23) — at p∗ each firm's two-period profit is δπ^{S∗}
-- statement:
--   In the two-period experience-goods duopoly, let $p^*=c-\delta(\pi^{R*}-\pi^{S*})$, and assume consumers buy at $p^*$, i.e. $u_0\le V-p^*$. When both firms charge $p^*$, firm $A$ has share $\lambda$, firm $B$ has share $1-\lambda$, and each firm's two-period profit equals
--
--   $$
--   \pi_i^*=\lambda_i(p^*-c)+\delta\bigl(\lambda_i\pi^{R*}+\lambda_{-i}\pi^{S*}\bigr)=\delta\pi^{S*},
--   $$
--
--   whatever the tie share $\lambda\in[0,1]$.
--
--   So each firm earns exactly the discounted second-period profit it would have earned with zero first-period market share, the profit from switching consumers.
--
--   **Formalization Note** The identity is stated for both firms, $\Pi_A(p^*,p^*)=\delta\pi^{S*}$ and $\Pi_B(p^*,p^*)=\delta\pi^{S*}$.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 21 (PDF 23), eq. (13)

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

namespace SpilloverDuopoly.Switchers

/-- Equation (13), p. 21: at the symmetric profile `(p∗, p∗)` each firm's two-period profit is
`λ_i (p∗ - c) + δ (λ_i π^{R∗} + λ_{-i} π^{S∗}) = δ π^{S∗}`. -/
theorem eq_13_profit (G : Params) (hS : G.Standing) (hcov : G.u0 ≤ G.CS G.pStar) :
    G.profitA G.pStar G.pStar = G.delta * G.piS ∧
    G.profitB G.pStar G.pStar = G.delta * G.piS := by sorry

end SpilloverDuopoly.Switchers
