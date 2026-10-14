-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_proposition_EC_13
-- name    : RetailPrivacy.SupplyChain.proposition_EC_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:47.99123+00:00
-- url     : https://prove2.me/theorems/e332ad0c-6806-458b-8da7-0c7ef2e7439e
-- title:
--   Proposition EC.13, p. ec15 — the GDPR's effect on the supplier's profit in the chain
-- statement:
--   In the supply chain, let $P_{\mathbb R}$ and $P_{\mathbb C}$ be any subgame-perfect equilibria under the ℝ mode and the ℂ mode (the GDPR), and let $\pi_s^{\mathbb R}$, $\pi_s^{\mathbb C}$ be the supplier's equilibrium profits. Then
--
--   1. if $v < 4\sqrt{1-\delta}$, then $\pi_s^{\mathbb R} < \pi_s^{\mathbb C}$ (the GDPR strictly increases the supplier's profit);
--   2. if $4\sqrt{1-\delta} < v < \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\pi_s^{\mathbb C} < \pi_s^{\mathbb R}$;
--   3. if $v > \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\pi_s^{\mathbb C} = \pi_s^{\mathbb R}$.
--
--   This is the supplier column of Theorem 2.
--
--   **Formalization Note** The paper's "otherwise" also covers $v = 4\sqrt{1-\delta}$ and $v = 4\sqrt{\mathcal M}/\mathcal Z$. At these points one retailer is indifferent about collecting, and the supplier's profit depends on her choice (at $c = 0.2$, $\delta = 0.8$, $v = 4\sqrt{1-\delta}$ it is about $0.62$ in the ℝ mode against $1.39$ or $0.40$ in the ℂ mode), so the clause is false there. It is stated only for $v > 4\sqrt{\mathcal M}/\mathcal Z$.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec15, Proposition EC.13; proof pp. ec35–ec36

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem proposition_EC_13 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 4 * Real.sqrt (1 - δ) → eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt (1 - δ) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ → eqSupplier v δ PC < eqSupplier v δ PR) ∧
      (4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v → eqSupplier v δ PC = eqSupplier v δ PR) := by sorry

end RetailPrivacy.SupplyChain
