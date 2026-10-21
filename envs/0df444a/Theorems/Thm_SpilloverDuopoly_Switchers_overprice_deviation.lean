-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_overprice_deviation
-- name    : SpilloverDuopoly.Switchers.overprice_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:35.75628+00:00
-- url     : https://prove2.me/theorems/0b42ff88-097c-40c3-85eb-fb8798d0e580
-- title:
--   Proof of Theorem 1, p. 20 (PDF 22) — pricing above p∗ leaves the deviator's profit unchanged
-- statement:
--   In the two-period experience-goods duopoly, let $p^*=c-\delta(\pi^{R*}-\pi^{S*})$, and assume consumers buy at $p^*$, i.e. $u_0\le V-p^*$. If a firm prices above its rival's price $p^*$, at any $p'>p^*$, it gives up its first-period share, and its two-period profit is unchanged:
--
--   $$
--   \Pi_A(p',\,p^*)=\Pi_A(p^*,p^*),\qquad \Pi_B(p^*,\,p')=\Pi_B(p^*,p^*).
--   $$
--
--   The deviator avoids the first-period margin $\lambda_i(p^*-c)$ but turns its share $\lambda_i$ from repeat into switching consumers. At $p^*$ these two effects cancel, so pricing above $p^*$ is not profitable.
--
--   **Formalization Note** The statement is given for both firms. The deviator then sells only in the second period, and the equality is also the paper's remark on p. 21 that such a firm earns $\delta\pi^{S*}$, the equilibrium profit.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 20 (PDF 22), proof of Theorem 1, third paragraph; also p. 21 (PDF 23)

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

namespace SpilloverDuopoly.Switchers

/-- Proof of Theorem 1, p. 20: pricing above `p∗` leaves the deviator's two-period profit
unchanged, so it is not profitable. Stated for firm A and for firm B. -/
theorem overprice_deviation (G : Params) (hS : G.Standing) (hcov : G.u0 ≤ G.CS G.pStar)
    (p' : ℝ) (hp' : G.pStar < p') :
    G.profitA p' G.pStar = G.profitA G.pStar G.pStar ∧
    G.profitB G.pStar p' = G.profitB G.pStar G.pStar := by sorry

end SpilloverDuopoly.Switchers
