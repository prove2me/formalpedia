-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_proposition_3
-- name    : RetailPrivacy.SupplyChain.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:43.825857+00:00
-- url     : https://prove2.me/theorems/c8c13738-758e-4350-bee9-99a9f8c2dfbb
-- title:
--   Proposition 3, p. 19 — the ℝ-mode chain equilibrium (r*, p*, w*, 𝒯₁(p*)) with and without collection; collect iff v ≤ 4√ℳ/𝒵
-- statement:
--   Consider the supply chain under the ℝ mode (retailer-controlled data). A subgame-perfect equilibrium exists, and every subgame-perfect equilibrium has the following outcomes.
--
--   1. In the subgame where the retailer collects data, the monetization intensity $r^*$, retail price $p^*$, wholesale price $w^*$ and sales quantity $\mathcal T_1(p^*)$ are
--   $$(r^*, p^*, w^*, \mathcal T_1(p^*)) = \begin{cases} \Big(\dfrac{v\delta\mathcal Z}{4\mathcal M},\ \dfrac{3v}{4} - \dfrac{vc\delta^2}{4\mathcal M},\ \dfrac v2,\ \dfrac{v\mathcal Z^2}{4\mathcal M}\Big) & \text{if } v \le \dfrac{4\mathcal M}{\mathcal Z^2},\\[2ex] \Big(\dfrac{\delta}{\mathcal Z},\ v - 1 + \dfrac{2c\delta}{\mathcal Z},\ v - \dfrac{2\mathcal M}{\mathcal Z^2},\ 1\Big) & \text{if } v > \dfrac{4\mathcal M}{\mathcal Z^2}.\end{cases}$$
--   2. In the subgame without collection,
--   $$(r^*, p^*, w^*, \mathcal T_1(p^*)) = \begin{cases} (0,\ 3v/4,\ v/2,\ v/4) & \text{if } v \le 4,\\ (0,\ v-1,\ v-2,\ 1) & \text{if } v > 4.\end{cases}$$
--   3. The retailer's equilibrium profit with collection is at least her profit without collection if and only if $v \le 4\sqrt{\mathcal M}/\mathcal Z$; moreover $4\mathcal M/\mathcal Z^2 \le 4\sqrt{\mathcal M}/\mathcal Z \le 4$.
--
--   This is the ℝ-mode equilibrium of the chain; together with Proposition 4 it gives every comparison of Theorem 2.
--
--   **Formalization Note** Part 3 is stated as the comparison of the retailer's subgame profits. The paper's "collects ($\ell^* = 1$) if and only if $v \le 4\sqrt{\mathcal M}/\mathcal Z$" breaks the tie at $v = 4\sqrt{\mathcal M}/\mathcal Z$ toward collecting; there both choices are subgame perfect, so "$\ell^* = 1$ in every equilibrium" would be false at that point. The standing assumption $v > 0$ is added (at $v \le 0$ nothing is sold).
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 19, Proposition 3; proof pp. ec24–ec25

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem proposition_3 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧
    ∀ P : Profile, IsSPE .R v c δ P →
      ((v ≤ 4 * RetailPrivacy.SingleFirm.Mc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 →
          (pathResp P true).2 = v * δ * RetailPrivacy.SingleFirm.Zc c δ / (4 * RetailPrivacy.SingleFirm.Mc c δ) ∧
          pathPrice P true = 3 * v / 4 - v * c * δ ^ 2 / (4 * RetailPrivacy.SingleFirm.Mc c δ) ∧
          pathWholesale P true = v / 2 ∧
          RetailPrivacy.SingleFirm.demand true v δ (pathPrice P true) (pathResp P true).2 = v * RetailPrivacy.SingleFirm.Zc c δ ^ 2 / (4 * RetailPrivacy.SingleFirm.Mc c δ)) ∧
       (4 * RetailPrivacy.SingleFirm.Mc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 < v →
          (pathResp P true).2 = δ / RetailPrivacy.SingleFirm.Zc c δ ∧
          pathPrice P true = v - 1 + 2 * c * δ / RetailPrivacy.SingleFirm.Zc c δ ∧
          pathWholesale P true = v - 2 * RetailPrivacy.SingleFirm.Mc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 ∧
          RetailPrivacy.SingleFirm.demand true v δ (pathPrice P true) (pathResp P true).2 = 1)) ∧
      ((v ≤ 4 →
          (pathResp P false).2 = 0 ∧ pathPrice P false = 3 * v / 4 ∧ pathWholesale P false = v / 2 ∧
          RetailPrivacy.SingleFirm.demand false v δ (pathPrice P false) (pathResp P false).2 = v / 4) ∧
       (4 < v →
          (pathResp P false).2 = 0 ∧ pathPrice P false = v - 1 ∧ pathWholesale P false = v - 2 ∧
          RetailPrivacy.SingleFirm.demand false v δ (pathPrice P false) (pathResp P false).2 = 1)) ∧
      ((retailerValue v c δ P false ≤ retailerValue v c δ P true ↔ v ≤ 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ) ∧
        4 * RetailPrivacy.SingleFirm.Mc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 ≤ 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ ∧ 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ ≤ 4) := by sorry

end RetailPrivacy.SupplyChain
