-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_corollary_EC_1
-- name    : RetailPrivacy.SupplyChain.corollary_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:42.641073+00:00
-- url     : https://prove2.me/theorems/767492f5-8123-41ba-875f-8cc1d24b9aac
-- title:
--   Corollary EC.1, p. ec14 — the retailer collects under both policies below 4√(1 − δ), only without the GDPR up to 4√ℳ/𝒵, never above
-- statement:
--   In the supply chain, let $P_{\mathbb R}$ be any subgame-perfect equilibrium under the ℝ mode and $P_{\mathbb C}$ any subgame-perfect equilibrium under the ℂ mode (the GDPR). Then
--
--   1. if $v < 4\sqrt{1-\delta}$, the retailer collects consumer data in both;
--   2. if $4\sqrt{1-\delta} < v < 4\sqrt{\mathcal M}/\mathcal Z$, she collects data in $P_{\mathbb R}$ and not in $P_{\mathbb C}$;
--   3. if $v > 4\sqrt{\mathcal M}/\mathcal Z$, she collects data in neither.
--
--   The GDPR thus shrinks the range of valuations in which the retailer collects data; this is the mechanism behind every case of Theorem 2.
--
--   **Formalization Note** The paper writes $v \le 4\sqrt{1-\delta}$ and $v \ge 4\sqrt{\mathcal M}/\mathcal Z$. At those two points the retailer is indifferent and both collection decisions are subgame perfect; the printed boundaries follow the tie-break of Propositions 3(iii) and 4(iii). The statement is posed with strict inequalities, which holds for every equilibrium. Existence of equilibria is part of Propositions 3 and 4.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. ec14, Corollary EC.1; proof p. ec32

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem corollary_EC_1 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 4 * Real.sqrt (1 - δ) → PR.collect = true ∧ PC.collect = true) ∧
      (4 * Real.sqrt (1 - δ) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ → PR.collect = true ∧ PC.collect = false) ∧
      (4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v → PR.collect = false ∧ PC.collect = false) := by sorry

end RetailPrivacy.SupplyChain
