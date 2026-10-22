-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_firm_trading_posteriors
-- name    : TimelyLoss.Feedback.firm_trading_posteriors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:48.303636+00:00
-- url     : https://prove2.me/theorems/b55c9f02-e1f7-4b76-8c35-4cc10cc6072d
-- title:
--   §3.2, p. 16 (PDF 17) — under trading, µ_F^{φ,1} = 1/(2−λ) > µ̄ and µ_F^{φ,−1} = (1−λ)/(2−λ) < µ̲
-- statement:
--   Consider the trading profile, in which an informed speculator buys on $H$ and sells on $L$ after a null report. Let $\mu_F^{\phi,X}=\Pr(\theta=H\mid X,\delta=\phi)$ be the posterior of an uninformed firm after order flow $X$. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. Then
--
--   $$\mu_F^{\phi,1}=\frac{1}{2-\lambda}>\bar\mu=\frac12+\frac{c}{2x},\qquad \mu_F^{\phi,-1}=\frac{1-\lambda}{2-\lambda}<\underline\mu=\frac12-\frac{c}{2x},$$
--
--   so an uninformed firm increases investment at $X=1$ and decreases it at $X=-1$.
--
--   This is the feedback effect: the order flow, through the speculator's information, changes the firm's real decision.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 16 (PDF 17), Trading equilibrium

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem firm_trading_posteriors (P : Params) (hP : P.Standing) :
    muF P T 1 = 1 / (2 - P.lam) ∧
    muF P T (-1) = (1 - P.lam) / (2 - P.lam) ∧
    muBar P < muF P T 1 ∧
    muF P T (-1) < muLow P ∧
    firmRule P (muF P T 1) = .up ∧
    firmRule P (muF P T (-1)) = .down := by sorry

end TimelyLoss.Feedback
