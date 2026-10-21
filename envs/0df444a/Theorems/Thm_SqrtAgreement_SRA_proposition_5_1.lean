-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_proposition_5_1
-- name    : SqrtAgreement.SRA.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:52.349988+00:00
-- url     : https://prove2.me/theorems/218b6588-5045-42a1-9d02-71081d1476b3
-- title:
--   Proposition 5.1, p. 27 — garbling by a reporting strategy q lowers the square root agreement measure by at least δΩ(q)²(|Y|−1)/(2√|Y|)
-- statement:
--   Let $(P_X,\mathbf p)$ be a generating model on finite sets $\mathcal X$ and $\mathcal Y$, and let $Y_1,Y_2$ be two responses drawn from it (conditionally i.i.d. given a common type). Let $Z_1,Z_2$ be obtained by applying a stochastic reporting strategy $\mathbf q$ independently to $Y_1$ and $Y_2$. With the square root agreement measure $\Gamma$, the Cauchy–Schwarz gap $\delta(P_X,\mathbf p)$ and the uninformativeness $\Omega(\mathbf q)$,
--   $$\Gamma(Z_1,Z_2)\ \le\ \Gamma(Y_1,Y_2)-\frac{\delta(P_X,\mathbf p)\,\Omega(\mathbf q)^2\,(|\mathcal Y|-1)}{2\sqrt{|\mathcal Y|}} .$$
--
--   Here $\Gamma(Y_1,Y_2)=\sum_y\sqrt{\sum_x P_X(x)p_y(x)^2}$ and $\Gamma(Z_1,Z_2)=\sum_y\sqrt{\sum_x P_X(x)\big(\sum_{y'}p_{y'}(x)q_y(y')\big)^2}$. Since the limiting payoff under a symmetric profile $\mathbf q$ is $K\Gamma(Z_1,Z_2)$, this monotonicity property is what makes fully informative reporting payoff-dominant among symmetric profiles.
--
--   **Formalization Note** $\Gamma(Z_1,Z_2)$ is formalized as the SRAM of the garbled model $(P_X,\mathbf p\circ\mathbf q)$, $(\mathbf p\circ\mathbf q)_y(x)=\sum_{y'}p_{y'}(x)q_y(y')$, which is the law of $Z$ given the type (first line of the proof, p. 51). When $|\mathcal Y|=1$ the formal $\delta$ is $0$ and the claim reduces to $\Gamma(Z_1,Z_2)\le\Gamma(Y_1,Y_2)$.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 27, Proposition 5.1, eq. (19)

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem proposition_5_1 {m k : ℕ} (G : GenModel m k) (q : Strat k) (hG : G.Valid)
    (hq : Stoch q) :
    (G.garble q).sram ≤
      G.sram - G.delta * uninf q ^ 2 * ((k : ℝ) - 1) / (2 * Real.sqrt (k : ℝ)) := by sorry

end SqrtAgreement.SRA
