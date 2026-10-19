-- Prove2me | Theorems.Thm_Teletriage_OneShot_pi_TT
-- name    : Teletriage.OneShot.pi_TT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:02.570708+00:00
-- url     : https://prove2.me/theorems/d20023eb-89d7-480a-8c58-efd38f49d0dc
-- title:
--   Display, p. 11 (PDF 11) — with teletriage π̃^ED(b) = b + β(1 − b) and π̃^DD(b) = αb on [b̲0, b̄0)
-- statement:
--   Assume the standing assumptions, informative teletriage ($\alpha+\beta<1$) and $\underline b_0<\bar b_0$. Let $\tilde\pi^{ED}(b)$ and $\tilde\pi^{DD}(b)$ be the probabilities that a patient with belief $b\in[0,1]$ ends up at the ED, resp. double-dips, when teletriage is available and she acts optimally (calling at most once and then following the no-teletriage rule at her posterior). Then
--   $$\tilde\pi^{ED}(b)=\begin{cases}1,&b\ge\bar b_0\\ b+\beta(1-b),&\underline b_0\le b<\bar b_0\\ b,&b<\underline b_0\end{cases}\qquad \tilde\pi^{DD}(b)=\begin{cases}0,&b\ge\bar b_0\\ \alpha b,&\underline b_0\le b<\bar b_0\\ b,&b<\underline b_0.\end{cases}$$
--
--   In the calling range, overtriage adds the ED visits $\beta(1-b)$ of sick patients predicted critical, while undertriage leaves the double-dipping $\alpha b$ of critical patients predicted sick.
--
--   **Formalization Note** The probabilities are computed from the optimal actions, with ties broken ED ≻ teletriage ≻ PCP; with this rule the display holds on all of $[0,1]$, endpoints included.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 11 (PDF 11), display of π̃^ED(b), π̃^DD(b)

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Display, p. 11: with informative teletriage and `b̲0 < b̄0`, `π̃^ED(b)` and `π̃^DD(b)` are
`1, 0` for `b ≥ b̄0`, `b + β(1 − b), αb` for `b̲0 ≤ b < b̄0`, and `b, b` for `b < b̲0`. -/
theorem pi_TT (P : Params) (hS : P.Standing) (hI : P.Informative) (hlh : bLow P < bHigh P)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    piEDtt P b = (if bHigh P ≤ b then 1 else if bLow P ≤ b then b + P.β * (1 - b) else b) ∧
    piDDtt P b = (if bHigh P ≤ b then 0 else if bLow P ≤ b then P.α * b else b) := by sorry

end Teletriage.OneShot
