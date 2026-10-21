-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_cheaper_takes_market
-- name    : SpilloverDuopoly.Switchers.cheaper_takes_market
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:28.026846+00:00
-- url     : https://prove2.me/theorems/07832101-4554-4445-9738-cd9cb326d04f
-- title:
--   Proof of Theorem 1, p. 20 (PDF 22) — consumers purchase the cheaper product in the first period
-- statement:
--   In the two-period experience-goods duopoly, let firm $i$ charge $p_i$ and its rival charge $p_{-i}$ in the first period. Suppose a consumer weakly prefers buying from the rival at $p_{-i}$ to not buying, $u_0\le V-p_{-i}$. Then firm $i$'s first-period share is
--
--   $$
--   \lambda_i(p_A,p_B)=\begin{cases}1 & p_i<p_{-i},\\ \text{its tie share} & p_i=p_{-i},\\ 0 & p_i>p_{-i},\end{cases}
--   $$
--
--   where the tie share is $\lambda$ for firm $A$ and $1-\lambda$ for firm $B$. Moreover, as soon as one of the two prices is acceptable ($u_0\le V-p_A$ or $u_0\le V-p_B$), the market is covered: $\lambda_A+\lambda_B=1$.
--
--   This is the first-period demand that the deviation arguments in the proof of Theorem 1 rely on.
--
--   **Formalization Note** The statement is given for both firms. The coverage hypothesis is what the paper's share rule needs for the cheaper good to be bought rather than the outside option.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 20 (PDF 22), proof of Theorem 1, first sentence; share rule §4, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

namespace SpilloverDuopoly.Switchers

/-- Proof of Theorem 1, p. 20, with the share rule of p. 15: consumers buy the cheaper good.
If the outside option does not beat the rival's price, a firm's share is `1`, its tie share or `0`
according as its price is lower than, equal to or higher than the rival's; and as soon as the
cheaper price is acceptable, the two shares add up to `1`. -/
theorem cheaper_takes_market (G : Params) (hS : G.Standing) (pA pB : ℝ) :
    (G.u0 ≤ G.CS pB →
      G.shareA pA pB = if pA < pB then 1 else if pA = pB then G.lam else 0) ∧
    (G.u0 ≤ G.CS pA →
      G.shareB pA pB = if pB < pA then 1 else if pB = pA then 1 - G.lam else 0) ∧
    (G.u0 ≤ G.CS pA ∨ G.u0 ≤ G.CS pB → G.shareA pA pB + G.shareB pA pB = 1) := by sorry

end SpilloverDuopoly.Switchers
