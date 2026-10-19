-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_equation_3_derivatives
-- name    : TimelyLoss.Feedback.equation_3_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:46.116122+00:00
-- url     : https://prove2.me/theorems/24e9cf76-ae7f-492f-957b-2e3ef2099e93
-- title:
--   Eq. (3), p. 15 (PDF 16), with dτ_L/dξ < 0 (p. 21) and dτ_H/dξ > 0 (p. 38) — probability the silent firm is informed
-- statement:
--   Let $\tau_\theta=\Pr(\delta=\theta\mid\theta,r=\phi)$ be the probability that a firm which issued a null report privately knows the state, given the state $\theta\in\{H,L\}$, with $\beta_H=\beta-\xi$ and $\beta_L=\beta+\xi$. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. For every feasible $\xi$ (that is, $0\le\beta\pm\xi\le1$):
--
--   1. for both states,
--   $$\tau_\theta=\frac{f(1-\beta_\theta)}{1-f\beta_\theta};$$
--   2. the derivatives in $\xi$ are
--   $$\frac{d\tau_L}{d\xi}=-\frac{f(1-f)}{(1-f\beta_L)^2}<0,\qquad \frac{d\tau_H}{d\xi}=\frac{f(1-f)}{(1-f\beta_H)^2}>0.$$
--
--   These derivatives are the information-endowment channel of Proposition 4: under timely loss recognition a silent firm in the bad state is less likely to be informed.
--
--   **Formalization Note** $\tau_\theta$ is defined as the Bayes ratio $f(1-\beta_\theta)/\Pr(r=\phi\mid\theta)$; the closed form (3) is to be proved.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), pp. 15, 21, 38 (PDF 16, 22, 39), Eq. (3), §4 and proof of Proposition 4

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem equation_3_derivatives (P : Params) (hP : P.Standing) (ξ : ℝ)
    (hξ : P.Feasible ξ) :
    (∀ θ : State,
      tau P ξ θ = P.f * (1 - betaOf P ξ θ) / (1 - P.f * betaOf P ξ θ)) ∧
    HasDerivAt (fun u => tau P u .L)
      (-(P.f * (1 - P.f)) / (1 - P.f * (P.β + ξ)) ^ 2) ξ ∧
    HasDerivAt (fun u => tau P u .H)
      (P.f * (1 - P.f) / (1 - P.f * (P.β - ξ)) ^ 2) ξ ∧
    -(P.f * (1 - P.f)) / (1 - P.f * (P.β + ξ)) ^ 2 < 0 ∧
    0 < P.f * (1 - P.f) / (1 - P.f * (P.β - ξ)) ^ 2 := by sorry

end TimelyLoss.Feedback
