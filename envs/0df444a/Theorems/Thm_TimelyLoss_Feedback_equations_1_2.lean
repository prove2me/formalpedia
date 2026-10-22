-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_equations_1_2
-- name    : TimelyLoss.Feedback.equations_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:46.365093+00:00
-- url     : https://prove2.me/theorems/98a2152c-a783-43c6-bfc7-d70a92597b62
-- title:
--   Eqs. (1)–(2), p. 14 (PDF 15) — t = 1/2 + (1/2)(f/(1−fβ))ξ and dt/dξ > 0
-- statement:
--   Let $t(\xi)=\Pr(\theta=H\mid r=\phi)$ be the market maker's belief in the good state after a null report and before any order flow, where informed firms report $H$ with probability $\beta-\xi$ and $L$ with probability $\beta+\xi$. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. For every feasible $\xi$ with $0\le\beta-\xi,\beta+\xi\le1$,
--
--   $$t(\xi)=\frac12+\frac12\,\frac{f}{1-f\beta}\,\xi,\qquad \frac{dt}{d\xi}=\frac12\,\frac{f}{1-f\beta}>0.$$
--
--   Under timely loss recognition ($\xi>0$) silence is good news: $t>1/2$. This is the state-uncertainty channel through which $\xi$ enters prices.
--
--   **Formalization Note** $t$ is defined by Bayes' rule from $\Pr(r=\phi\mid\theta)=(1-f)+f(1-\beta_\theta)$; the closed form and the derivative are to be proved. Feasibility keeps both disclosure rates in $[0,1]$; the Bayes denominator equals $1-f\beta>0$.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 14 (PDF 15), Eqs. (1)–(2)

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem equations_1_2 (P : Params) (hP : P.Standing) (ξ : ℝ)
    (hξ : P.Feasible ξ) :
    tNull P ξ = 1 / 2 + (1 / 2) * (P.f / (1 - P.f * P.β)) * ξ ∧
    HasDerivAt (tNull P) ((1 / 2) * (P.f / (1 - P.f * P.β))) ξ ∧
    0 < (1 / 2 : ℝ) * (P.f / (1 - P.f * P.β)) := by sorry

end TimelyLoss.Feedback
