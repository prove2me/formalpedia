-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_proposition_EC_11
-- name    : RetailPrivacy.SupplyChain.proposition_EC_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:40.032026+00:00
-- url     : https://prove2.me/theorems/af34033c-3a55-425d-8acb-a693f83f4ff6
-- title:
--   Proposition EC.11, p. ec14 — the GDPR's effect on consumer surplus in the chain
-- statement:
--   In the supply chain, let $P_{\mathbb R}$ and $P_{\mathbb C}$ be any subgame-perfect equilibria under the ℝ mode and the ℂ mode (the GDPR), and let $\mathrm{CS}_{\mathbb R}$, $\mathrm{CS}_{\mathbb C}$ be their equilibrium consumer surpluses. Then
--
--   1. if $v < \dfrac{4\mathcal M\sqrt{1-\delta}}{\mathcal Z\sqrt{\mathcal F}}$ or $\dfrac{4\sqrt{\mathcal F}}{\mathcal Z} < v < \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\mathrm{CS}_{\mathbb R} < \mathrm{CS}_{\mathbb C}$ (the GDPR strictly increases consumer surplus);
--   2. if $\dfrac{4\mathcal M\sqrt{1-\delta}}{\mathcal Z\sqrt{\mathcal F}} < v < \dfrac{4\sqrt{\mathcal F}}{\mathcal Z}$, then $\mathrm{CS}_{\mathbb C} < \mathrm{CS}_{\mathbb R}$;
--   3. if $v = \dfrac{4\mathcal M\sqrt{1-\delta}}{\mathcal Z\sqrt{\mathcal F}}$, or $v = \dfrac{4\sqrt{\mathcal F}}{\mathcal Z}$, or $v > \dfrac{4\sqrt{\mathcal M}}{\mathcal Z}$, then $\mathrm{CS}_{\mathbb C} = \mathrm{CS}_{\mathbb R}$.
--
--   This is the consumer-surplus column of Theorem 2.
--
--   **Formalization Note** The paper's part (iii), "otherwise", also covers $v = 4\sqrt{\mathcal M}/\mathcal Z$. There the ℝ-mode retailer is indifferent between collecting and not; under the paper's own tie-break (she collects) the consumer surplus differs from the ℂ mode's, so the clause would be false. It is stated without that point.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec14, Proposition EC.11; proof pp. ec32–ec34

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem proposition_EC_11 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) ∨ (4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ) → eqCS v δ PR < eqCS v δ PC) ∧
      (4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ → eqCS v δ PC < eqCS v δ PR) ∧
      (v = 4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) ∨ v = 4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ ∨ 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v → eqCS v δ PC = eqCS v δ PR) := by sorry

end RetailPrivacy.SupplyChain
