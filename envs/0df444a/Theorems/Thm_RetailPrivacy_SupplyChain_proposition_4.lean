-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_proposition_4
-- name    : RetailPrivacy.SupplyChain.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:47.340682+00:00
-- url     : https://prove2.me/theorems/71e7eb09-c2d8-47a9-bddb-bf51938ae0f1
-- title:
--   Proposition 4, p. 22 — the ℂ-mode chain equilibrium (p̃*, w̃*, 𝒯₂(p̃*)) with and without collection; collect iff v ≤ 4√(1 − δ)
-- statement:
--   Consider the supply chain under the ℂ mode (consumer-controlled data, the GDPR). A subgame-perfect equilibrium exists, and every subgame-perfect equilibrium has the following outcomes.
--
--   1. In the subgame where the retailer collects data, the retail price $\tilde p^*$, wholesale price $\tilde w^*$ and sales quantity $\mathcal T_2(\tilde p^*)$ are
--   $$(\tilde p^*, \tilde w^*, \mathcal T_2(\tilde p^*)) = \begin{cases} \Big(\dfrac{3v}{4},\ \dfrac v2,\ \dfrac{v}{4(1-\delta)}\Big) & \text{if } v \le 4(1-\delta),\\[2ex] \big(v - (1-\delta),\ v - 2(1-\delta),\ 1\big) & \text{if } v > 4(1-\delta).\end{cases}$$
--   2. In the subgame without collection,
--   $$(\tilde p^*, \tilde w^*, \mathcal T_2(\tilde p^*)) = \begin{cases} (3v/4,\ v/2,\ v/4) & \text{if } v \le 4,\\ (v-1,\ v-2,\ 1) & \text{if } v > 4.\end{cases}$$
--   3. The retailer's equilibrium profit with collection is at least her profit without collection if and only if $v \le 4\sqrt{1-\delta}$; moreover $4(1-\delta) \le 4\sqrt{1-\delta} \le 4$.
--
--   Together with Proposition 3 this gives every comparison of Theorem 2.
--
--   **Formalization Note** As in Proposition 3, part 3 is the comparison of the retailer's subgame profits, which is the paper's "collects iff $v \le 4\sqrt{1-\delta}$" with its tie broken toward collecting. Part 2 also records $r = 0$ (no collection). The standing assumption $v > 0$ is added.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 22, Proposition 4; proof p. ec25

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem proposition_4 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ P : Profile, IsSPE .C v c δ P →
      ((v ≤ 4 * (1 - δ) →
          pathPrice P true = 3 * v / 4 ∧
          pathWholesale P true = v / 2 ∧
          RetailPrivacy.SingleFirm.demand true v δ (pathPrice P true) (pathResp P true).2 = v / (4 * (1 - δ))) ∧
       (4 * (1 - δ) < v →
          pathPrice P true = v - (1 - δ) ∧
          pathWholesale P true = v - 2 * (1 - δ) ∧
          RetailPrivacy.SingleFirm.demand true v δ (pathPrice P true) (pathResp P true).2 = 1)) ∧
      ((v ≤ 4 →
          (pathResp P false).2 = 0 ∧ pathPrice P false = 3 * v / 4 ∧ pathWholesale P false = v / 2 ∧
          RetailPrivacy.SingleFirm.demand false v δ (pathPrice P false) (pathResp P false).2 = v / 4) ∧
       (4 < v →
          (pathResp P false).2 = 0 ∧ pathPrice P false = v - 1 ∧ pathWholesale P false = v - 2 ∧
          RetailPrivacy.SingleFirm.demand false v δ (pathPrice P false) (pathResp P false).2 = 1)) ∧
      ((retailerValue v c δ P false ≤ retailerValue v c δ P true ↔ v ≤ 4 * Real.sqrt (1 - δ)) ∧
        4 * (1 - δ) ≤ 4 * Real.sqrt (1 - δ) ∧ 4 * Real.sqrt (1 - δ) ≤ 4) := by sorry

end RetailPrivacy.SupplyChain
