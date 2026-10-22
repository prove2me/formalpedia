-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_corollary_2_i
-- name    : TimelyLoss.Feedback.corollary_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:53.95936+00:00
-- url     : https://prove2.me/theorems/354ffd48-43e6-408b-b957-efcb29c74b40
-- title:
--   Corollary 2(i), p. 18 (PDF 19) — under neutral disclosure ξ = 0, π^T_sell < π^T_buy
-- statement:
--   Under the neutral disclosure policy $\xi=0$, in the trading profile the speculator's gross profit from selling on bad news is strictly smaller than her gross profit from buying on good news. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$.
--
--   $$\pi^T_{sell}\big|_{\xi=0}<\pi^T_{buy}\big|_{\xi=0}.$$
--
--   The asymmetry is the feedback effect: a negative order flow leads the firm to divest, which raises firm value in the bad state and lowers the short seller's gain. It identifies $\kappa^T=\pi^T_{sell}$ near $\xi=0$.
--
--   **Formalization Note** The strict inequality needs $f<1$ and $\lambda<1$, which the standing predicate makes explicit; at either endpoint the two profits are equal. Part (ii) of Corollary 2 is not formalized: its middle inequality fails for some admissible parameters.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 18 (PDF 19), Corollary 2(i)

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem corollary_2_i (P : Params) (hP : P.Standing) :
    piTsell P 0 < piTbuy P 0 := by sorry

end TimelyLoss.Feedback
