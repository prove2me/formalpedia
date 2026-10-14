-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_proposition_EC_12
-- name    : RetailPrivacy.SupplyChain.proposition_EC_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:37.947003+00:00
-- url     : https://prove2.me/theorems/985f2274-b17b-415c-b8cf-387563d7181a
-- title:
--   Proposition EC.12, p. ec14 — the GDPR's effect on the retailer's profit in the chain
-- statement:
--   In the supply chain, let $P_{\mathbb R}$ and $P_{\mathbb C}$ be any subgame-perfect equilibria under the ℝ mode and the ℂ mode (the GDPR), and let $\pi_r^{\mathbb R}$, $\pi_r^{\mathbb C}$ be the retailer's equilibrium profits. Then
--
--   1. if $v < \dfrac{4\sqrt{(1-\delta)\mathcal M}}{\mathcal Z}$, then $\pi_r^{\mathbb R} < \pi_r^{\mathbb C}$ (the GDPR strictly increases the retailer's profit);
--   2. if $\dfrac{4\sqrt{(1-\delta)\mathcal M}}{\mathcal Z} < v < \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\pi_r^{\mathbb C} < \pi_r^{\mathbb R}$;
--   3. if $v = \dfrac{4\sqrt{(1-\delta)\mathcal M}}{\mathcal Z}$ or $v \ge \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\pi_r^{\mathbb C} = \pi_r^{\mathbb R}$.
--
--   This is the retailer column of Theorem 2.
--
--   **Formalization Note** "Otherwise" is stated in full: at $v = 4\sqrt{\mathcal M}/\mathcal Z$ the retailer's profit is the same whichever collection decision she takes.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec14, Proposition EC.12; proof pp. ec34–ec35

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem proposition_EC_12 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ → eqRetailer v c δ PR < eqRetailer v c δ PC) ∧
      (4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ → eqRetailer v c δ PC < eqRetailer v c δ PR) ∧
      (v = 4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ ∨ 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ ≤ v → eqRetailer v c δ PC = eqRetailer v c δ PR) := by sorry

end RetailPrivacy.SupplyChain
