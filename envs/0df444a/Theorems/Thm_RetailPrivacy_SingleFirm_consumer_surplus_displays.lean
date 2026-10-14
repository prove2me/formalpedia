-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_consumer_surplus_displays
-- name    : RetailPrivacy.SingleFirm.consumer_surplus_displays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:33.956149+00:00
-- url     : https://prove2.me/theorems/11f1bae9-ad85-4647-a993-3bd96c00f8ce
-- title:
--   Proof of Theorem 1, p. ec23 — equilibrium consumer surplus under the ℝ mode and under the ℂ mode
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$, with $\mathcal Z,\mathcal M,\mathcal F$ as in the model. In every subgame-perfect equilibrium of the $\mathbb R$ mode the on-path consumer surplus is
--   $$CS_{\mathbb R} = \begin{cases} \dfrac{v^2\mathcal Z^2\mathcal F}{8\mathcal M^2} & \text{if } v\le \dfrac{2\mathcal M}{\mathcal Z^2},\\[3mm] \dfrac{\mathcal F}{2\mathcal Z^2} & \text{if } v> \dfrac{2\mathcal M}{\mathcal Z^2},\end{cases}$$
--   and in every subgame-perfect equilibrium of the $\mathbb C$ mode it is
--   $$CS_{\mathbb C} = \begin{cases} \dfrac{v^2}{8(1-\delta)} & \text{if } v\le 2(1-\delta),\\[3mm] \dfrac{1-\delta}{2} & \text{if } v> 2(1-\delta).\end{cases}$$
--
--   These are the two surplus curves compared in Theorem 1. The consumer surplus is the integral over $\theta\in[0,1]$ of each consumer's realized utility, including the exploitation loss $r^*\delta$ of disclosing buyers in the $\mathbb R$ mode.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec23, Proof of Theorem 1, first and second displays

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem consumer_surplus_displays (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hv : 0 < v) :
    (∀ PR : Profile, IsSPE .R v c δ PR →
      eqCS v δ PR =
        if v ≤ 2 * Mc c δ / Zc c δ ^ 2 then
          v ^ 2 * Zc c δ ^ 2 * Fc c δ / (8 * Mc c δ ^ 2)
        else Fc c δ / (2 * Zc c δ ^ 2)) ∧
    (∀ PC : Profile, IsSPE .C v c δ PC →
      eqCS v δ PC =
        if v ≤ 2 * (1 - δ) then v ^ 2 / (8 * (1 - δ)) else (1 - δ) / 2) := by sorry

end RetailPrivacy.SingleFirm
