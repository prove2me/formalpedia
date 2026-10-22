-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_proposition_1_forms
-- name    : TimelyLoss.Feedback.proposition_1_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:56.063254+00:00
-- url     : https://prove2.me/theorems/c0ed0ec4-72cd-4e44-b2f7-3074d91c46d4
-- title:
--   Proposition 1, p. 15 (PDF 16), closed forms of π^NT — π^NT_sell = (2/3)t(R′_H − R′_L), π^NT_buy = (2/3)(1−t)(R′_H − R′_L)
-- statement:
--   In the no-trading profile the speculator does not trade, so on path the order flow carries no information; off path, $X=2$ is read as good news and $X=-2$ as bad news. Let $\pi^{NT}_{sell}$ ($\pi^{NT}_{buy}$) be the expected gross profit of an informed speculator who deviates and sells on $\eta=L$ (buys on $\eta=H$) after a null report. With $t=\Pr(\theta=H\mid r=\phi)$, $\tau_\theta$ the probability that the silent firm is informed, and $R'_\theta=R_\theta+\tau_\theta(x-c)$: Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. For every feasible $\xi$,
--
--   $$\pi^{NT}_{sell}=\frac23\,t\,(R'_H-R'_L),\qquad \pi^{NT}_{buy}=\frac23\,(1-t)\,(R'_H-R'_L).$$
--
--   These formulas give the no-trading threshold $\kappa^{NT}=\max\{\pi^{NT}_{buy},\pi^{NT}_{sell}\}$ of Proposition 1.
--
--   **Formalization Note** The profits are computed from the Bayesian prices and the firm's response in the model, so the two identities have content. The equilibrium-existence clause of Proposition 1 is not part of this item.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 15 (PDF 16), Proposition 1, profit formulas

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem proposition_1_forms (P : Params) (hP : P.Standing) (ξ : ℝ)
    (hξ : P.Feasible ξ) :
    piNTsell P ξ = (2 / 3 : ℝ) * tNull P ξ * (Rprime P ξ .H - Rprime P ξ .L) ∧
    piNTbuy P ξ = (2 / 3 : ℝ) * (1 - tNull P ξ) *
      (Rprime P ξ .H - Rprime P ξ .L) := by sorry

end TimelyLoss.Feedback
