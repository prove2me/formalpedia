-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_corollary_1
-- name    : TimelyLoss.Feedback.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:46.327754+00:00
-- url     : https://prove2.me/theorems/ed2ab4a9-a0e9-48a5-9639-ab6e6073685f
-- title:
--   Corollary 1, p. 16 (PDF 17) — under neutral disclosure ξ = 0, π^NT_sell = π^NT_buy
-- statement:
--   Under the neutral disclosure policy $\xi=0$ (good and bad news are reported equally promptly), the speculator's gross profits from deviating from the no-trading profile by selling on bad news and by buying on good news coincide. Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$.
--
--   $$\pi^{NT}_{sell}\big|_{\xi=0}=\pi^{NT}_{buy}\big|_{\xi=0}.$$
--
--   This is the symmetric reference point against which Proposition 4(iii) compares the no-trading threshold.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 16 (PDF 17), Corollary 1

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem corollary_1 (P : Params) (hP : P.Standing) :
    piNTsell P 0 = piNTbuy P 0 := by sorry

end TimelyLoss.Feedback
