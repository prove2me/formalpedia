-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_proposition_4
-- name    : TimelyLoss.Feedback.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:57.092946+00:00
-- url     : https://prove2.me/theorems/af0b29a4-d81f-4c70-8e56-c7f52a8c7101
-- title:
--   Proposition 4, p. 20 (PDF 21) — timely loss recognition raises π^T_sell, π^NT_sell, κ^T near ξ = 0, and κ^NT
-- statement:
--   In the feedback trading game, $\xi=\tfrac12(\beta_L-\beta_H)$ measures how much more promptly bad news is reported than good news; $\xi>0$ is timely loss recognition. Let $\pi^T_{buy},\pi^T_{sell}$ be the speculator's gross profits in the trading profile, $\pi^{NT}_{buy},\pi^{NT}_{sell}$ her gross deviation profits in the no-trading profile, $\kappa^T=\min\{\pi^T_{buy},\pi^T_{sell}\}$ and $\kappa^{NT}=\max\{\pi^{NT}_{buy},\pi^{NT}_{sell}\}$, all as functions of $\xi$. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. Then:
--
--   1. at every feasible $\xi$ ($0\le\beta\pm\xi\le1$), both selling profits are differentiable with positive derivative,
--   $$\frac{d\pi^T_{sell}}{d\xi}>0,\qquad \frac{d\pi^{NT}_{sell}}{d\xi}>0;$$
--   2. there is an open interval around $\xi=0$ on which $\kappa^T$ is differentiable with positive derivative;
--   3. for every feasible $\hat\xi>0$,
--   $$\kappa^{NT}(\hat\xi)>\kappa^{NT}(0),\qquad \kappa^{NT}(\hat\xi)>\kappa^{NT}(-\hat\xi).$$
--
--   So timely loss recognition widens the range of trading costs supporting trading near neutral reporting, and narrows the range supporting no trading, relative to both neutral reporting and the mirrored timely-gain policy.
--
--   **Formalization Note** The profits are computed from the Bayesian order-flow prices and the firm's response in the model, not defined by the closed forms (8)–(9). Derivatives are stated as `HasDerivAt` with a positive value. Clause 2 reads "$d\min\{\pi^T_{buy},\pi^T_{sell}\}/d\xi|_{\xi=0}>0$ in the neighborhood around $\xi=0$" as a positive derivative throughout some open interval containing $0$; it is not claimed on the whole feasible range, where the minimum can switch to $\pi^T_{buy}$. $\hat\xi$ is restricted to feasible values, as in §5.1 (p. 23).
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 20 (PDF 21), Proposition 4

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem proposition_4 (P : Params) (hP : P.Standing) :
    (∀ ξ : ℝ, P.Feasible ξ →
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (piTsell P) d ξ) ∧
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (piNTsell P) d ξ)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ ξ ∈ Set.Ioo (-ε) ε,
      ∃ d : ℝ, 0 < d ∧ HasDerivAt (kappaT P) d ξ) ∧
    (∀ ξh : ℝ, 0 < ξh → P.Feasible ξh →
      kappaNT P 0 < kappaNT P ξh ∧
      kappaNT P (-ξh) < kappaNT P ξh) := by sorry

end TimelyLoss.Feedback
