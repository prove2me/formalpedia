-- Prove2me | Theorems.Thm_TradeCredit_Terms_corollary3_Q_monotone
-- name    : TradeCredit.Terms.corollary3_Q_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:47.652038+00:00
-- url     : https://prove2.me/theorems/19db3d37-0ce5-486e-aa57-0dbf27b8e2d5
-- title:
--   Corollary 3, p. 12 — Q(θ_b, θ_t) increases in θ_b and in θ_t on Θ
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3, and let $0<c<1$, $\alpha_b\in[0,1]$ and $K>0$. Let $\Theta$ be the threshold domain and
--   $$Q(\theta_b,\theta_t)=\min\{q\ge 0:\ q\bar F(q)=[\theta_t+C(\theta_b)]\,\bar F(\theta_t)\}$$
--   the order quantity induced by the thresholds. Then:
--   1. for every fixed $\theta_t$, $\theta_b\mapsto Q(\theta_b,\theta_t)$ is (weakly) increasing on $\{\theta_b:(\theta_b,\theta_t)\in\Theta\}$;
--   2. for every fixed $\theta_b$, $\theta_t\mapsto Q(\theta_b,\theta_t)$ is (weakly) increasing on $\{\theta_t:(\theta_b,\theta_t)\in\Theta\}$.
--
--   This is the operating-cost channel in the supplier's trade-off: offering more trade credit (larger $\theta_t$) or a deeper early-payment discount (larger $\theta_b$) raises the quantity the supplier must produce.
--
--   **Formalization Note** Only the second paragraph of Corollary 3 is formalized: the claim that $Q$ increases in both thresholds. The first paragraph (a one-to-one mapping between $\Theta$ and contracts $(w_c,w_t)$ under the retailer's best response of Proposition 1) is the paper's reduction from contracts to thresholds; it is built into the model, not stated. $\Theta$ includes the constraints $\theta_t\le Q$ and $c\le w_c$, the image of §3.1's $c\le w_c\le w_t\le 1$ under (11). "Increases" is read weakly.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 12, Corollary 3 (second paragraph); proof p. 35

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem corollary3_Q_monotone (f : ℝ → ℝ) (hf : DemandModel f)
    (c αb K : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1) (hK : 0 < K) :
    (∀ θt : ℝ, MonotoneOn (fun θb => Qfun f αb K θb θt) {θb : ℝ | (θb, θt) ∈ Theta f c αb K}) ∧
      (∀ θb : ℝ, MonotoneOn (fun θt => Qfun f αb K θb θt) {θt : ℝ | (θb, θt) ∈ Theta f c αb K}) := by sorry

end TradeCredit.Terms
