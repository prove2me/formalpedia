-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_profit_displays
-- name    : RetailPrivacy.SingleFirm.profit_displays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:43.69156+00:00
-- url     : https://prove2.me/theorems/aa3b5ece-07f1-4cdb-9a75-15c60103b110
-- title:
--   Proof of Theorem 1, p. ec23 — equilibrium profit of the firm under the ℝ mode and under the ℂ mode
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$. In every subgame-perfect equilibrium of the $\mathbb R$ mode the firm's on-path profit is
--   $$\pi_{\mathbb R} = \begin{cases} \dfrac{v^2\mathcal Z^2}{4\mathcal M} & \text{if } v\le \dfrac{2\mathcal M}{\mathcal Z^2},\\[3mm] v-\dfrac{\mathcal M}{\mathcal Z^2} & \text{if } v> \dfrac{2\mathcal M}{\mathcal Z^2},\end{cases}$$
--   and in every subgame-perfect equilibrium of the $\mathbb C$ mode it is
--   $$\pi_{\mathbb C} = \begin{cases} \dfrac{v^2}{4(1-\delta)} & \text{if } v\le 2(1-\delta),\\[3mm] v-(1-\delta) & \text{if } v> 2(1-\delta).\end{cases}$$
--
--   The $\mathbb R$-mode profit includes the exploitation profit $r^*\delta s^* - c (r^*)^2$. Together with the consumer-surplus displays these give the profit and welfare comparisons of Theorem 1.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec23, Proof of Theorem 1, third and fourth displays

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem profit_displays (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∀ PR : Profile, IsSPE .R v c δ PR →
      eqProfit v c δ PR =
        if v ≤ 2 * Mc c δ / Zc c δ ^ 2 then v ^ 2 * Zc c δ ^ 2 / (4 * Mc c δ)
        else v - Mc c δ / Zc c δ ^ 2) ∧
    (∀ PC : Profile, IsSPE .C v c δ PC →
      eqProfit v c δ PC =
        if v ≤ 2 * (1 - δ) then v ^ 2 / (4 * (1 - δ)) else v - (1 - δ)) := by sorry

end RetailPrivacy.SingleFirm
