-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_undercut_deviation
-- name    : SpilloverDuopoly.Switchers.undercut_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:21.995707+00:00
-- url     : https://prove2.me/theorems/361afca6-9de2-4ad4-bec6-9f3090500ab9
-- title:
--   Proof of Theorem 1, p. 20 (PDF 22) — undercutting p∗ by ϵ > 0 lowers the deviator's profit by exactly ϵ
-- statement:
--   In the two-period experience-goods duopoly, let $p^*=c-\delta(\pi^{R*}-\pi^{S*})$, and assume consumers buy at $p^*$, i.e. $u_0\le V-p^*$. If a firm undercuts its rival's price $p^*$ by $\epsilon>0$, it captures the whole market, and its two-period profit falls by exactly $\epsilon$:
--
--   $$
--   \Pi_A(p^*-\epsilon,\,p^*)=\Pi_A(p^*,p^*)-\epsilon,\qquad \Pi_B(p^*,\,p^*-\epsilon)=\Pi_B(p^*,p^*)-\epsilon .
--   $$
--
--   The deviator gains the rival's share as repeat consumers, worth $\delta\lambda_{-i}(\pi^{R*}-\pi^{S*})$ in the second period. It pays for this in the first period, and $p^*$ is the price at which the two balance up to the $\epsilon$. So undercutting $p^*$ is never profitable.
--
--   **Formalization Note** The paper counts the first-period cost of the deviation as $\lambda_{-i}(c-p^*+\epsilon)$. The deviator also gives up $\epsilon$ on its own share $\lambda_i$, so the exact change in profit is $-\lambda_{-i}\epsilon-\lambda_i\epsilon=-\epsilon$. The statement records this exact value. The paper's conclusion, that the deviation is not profitable, is the same.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 20 (PDF 22), proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

namespace SpilloverDuopoly.Switchers

/-- Proof of Theorem 1, p. 20: undercutting `p∗` by `ε > 0` changes the deviator's two-period
profit by exactly `-ε`, so it is not profitable. Stated for firm A and for firm B. -/
theorem undercut_deviation (G : Params) (hS : G.Standing) (hcov : G.u0 ≤ G.CS G.pStar)
    (ε : ℝ) (hε : 0 < ε) :
    G.profitA (G.pStar - ε) G.pStar = G.profitA G.pStar G.pStar - ε ∧
    G.profitB G.pStar (G.pStar - ε) = G.profitB G.pStar G.pStar - ε := by sorry

end SpilloverDuopoly.Switchers
