-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_eq_5
-- name    : RetailPrivacy.SupplyChain.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:35.490211+00:00
-- url     : https://prove2.me/theorems/e8c7c054-df89-4398-a50f-3c7bc4874b77
-- title:
--   Display (5), p. 19 — the retailer's best response p(w) = (v + w)/2 − cδ²(v − w)/(2ℳ) on its unsaturated range
-- statement:
--   Consider the ℝ mode with data collection in the supply chain. Fix a wholesale price $w < v$ with
--   $$(v - w)\,\mathcal Z^2 \le 2\mathcal M,$$
--   and let the consumer stage at every retail price $p$ be its rational expectations equilibrium. Then the retailer's profit $\pi_r(w, p) = (p-w)\mathcal T_1(p) + r(p)\delta[\mathcal T_1(p) - r(p)] - c r(p)^2$ (4) is maximized over all $p \in \mathbb R$ at exactly one price,
--   $$p(w) = \frac{v + w}{2} - \frac{c\delta^2 (v - w)}{2\mathcal M}.$$
--
--   Display (5) is the retailer's pricing reaction to the supplier's wholesale price; the supplier's problem in Proposition 3 is solved by plugging it in.
--
--   **Formalization Note** The paper states (5) for every $w$. It is the best response only when $w < v$ and $(v-w)\mathcal Z^2 \le 2\mathcal M$; otherwise the retailer's best response saturates the market at $p = v - 1 + 2c\delta/\mathcal Z$ (or nobody is served when $w \ge v$). The statement is restricted to that range. The consumer response is any function $\rho$ giving an REE at every price; the REE is unique, so this is no loss.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 19, display (5) and profit (4)

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem eq_5 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (w : ℝ) (hw : w < v) (hrange : (v - w) * RetailPrivacy.SingleFirm.Zc c δ ^ 2 ≤ 2 * RetailPrivacy.SingleFirm.Mc c δ)
    (ρ : ℝ → ℝ × ℝ) (hρ : ∀ p, RetailPrivacy.SingleFirm.IsREE .R true v c δ p (ρ p).1 (ρ p).2) (p : ℝ) :
    IsMaxOn (fun p' => retailerProfit true v c δ w p' (ρ p')) Set.univ p ↔
      p = (v + w) / 2 - c * δ ^ 2 * (v - w) / (2 * RetailPrivacy.SingleFirm.Mc c δ) := by sorry

end RetailPrivacy.SupplyChain
