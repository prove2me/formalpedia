-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_proposition_2_forms
-- name    : TimelyLoss.Feedback.proposition_2_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:06.458759+00:00
-- url     : https://prove2.me/theorems/5e2c2e9c-e63d-4844-bded-2f86c4befb15
-- title:
--   Proposition 2, Eqs. (6)–(9), pp. 16–17 (PDF 17–18), closed forms of π^T and of µ_M^{φ,±1}
-- statement:
--   In the trading profile an informed speculator buys on $\eta=H$ and sells on $\eta=L$ after a null report. Let $t$, $\tau_\theta$ and $R'_\theta=R_\theta+\tau_\theta(x-c)$ be as in the model, and let $\mu_M^{\phi,X}=\Pr(\theta=H\mid X,r=\phi)$ be the market maker's posterior. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. For every feasible $\xi$:
--
--   1. the posteriors at $X=\pm1$ are
--   $$\mu_M^{\phi,1}=\frac{t}{t+(1-t)(1-\lambda)},\qquad \mu_M^{\phi,-1}=\frac{t(1-\lambda)}{t(1-\lambda)+(1-t)};$$
--   2. the gross profits from buying and selling are
--   $$\pi^T_{buy}=\tfrac13(1-t)\,[R'_H-R'_L]+\tfrac13\,(1-\mu_M^{\phi,1})\,[R_H-R_L+2(1-\tau_L)x],$$
--   $$\pi^T_{sell}=\tfrac13\,t\,[R'_H-R'_L]+\tfrac13\,\mu_M^{\phi,-1}\,[R_H-R_L-2(1-\tau_H)x].$$
--
--   These formulas give the trading threshold $\kappa^T=\min\{\pi^T_{buy},\pi^T_{sell}\}$ of Proposition 2.
--
--   **Formalization Note** The profits and posteriors are computed from the model's Bayesian prices and the firm's response. The inequalities $\mu_M^{\phi,1}>1/2$ and $\mu_M^{\phi,-1}<1/2$ printed after (6)–(7) are not included: they fail at some feasible $\xi<0$ (e.g. $f=0.95$, $\beta=1/2$, $\xi=-1/2$, $\lambda=0.7$ gives $\mu_M^{\phi,1}\approx0.14$). The equilibrium-existence clause of Proposition 2 is not part of this item.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), pp. 16–17 (PDF 17–18), Eqs. (6)–(9) and Proposition 2, profit formulas

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem proposition_2_forms (P : Params) (hP : P.Standing) (ξ : ℝ)
    (hξ : P.Feasible ξ) :
    muM P T ξ 1 = tNull P ξ /
      (tNull P ξ + (1 - tNull P ξ) * (1 - P.lam)) ∧
    muM P T ξ (-1) = tNull P ξ * (1 - P.lam) /
      (tNull P ξ * (1 - P.lam) + (1 - tNull P ξ)) ∧
    piTbuy P ξ = (1 / 3 : ℝ) * (1 - tNull P ξ) *
      (Rprime P ξ .H - Rprime P ξ .L) +
      (1 / 3 : ℝ) * (1 - muM P T ξ 1) *
      (P.RH - P.RL + 2 * (1 - tau P ξ .L) * P.x) ∧
    piTsell P ξ = (1 / 3 : ℝ) * tNull P ξ *
      (Rprime P ξ .H - Rprime P ξ .L) +
      (1 / 3 : ℝ) * muM P T ξ (-1) *
      (P.RH - P.RL - 2 * (1 - tau P ξ .H) * P.x) := by sorry

end TimelyLoss.Feedback
