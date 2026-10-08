-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_purchaseProfile_mul_level_le_roValue
-- name    : RevenueOrdered.PurchaseRatio.purchaseProfile_mul_level_le_roValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:07.625959+00:00
-- url     : https://prove2.me/theorems/c95d5b4f-3909-456d-a65f-00c17bb45da4
-- title:
--   Inequality (6) — N_i r_i ≤ RO for every i ∈ [k]
-- statement:
--   Fix a regular discrete choice model $\mathcal P$ on a nonempty finite product set and a revenue function $r>0$ with distinct values $r_1<\dots<r_k$. Let $\mathrm{RO}=\max_{1\le j\le k}\mathrm{rev}(S_j)$ be the revenue of the revenue-ordered assortments strategy, and let $N_i$ be the purchase profile of an assortment $S^*$. Then for every $i\in[k]$
--   $$
--   N_i\,r_i\;\le\;\mathrm{RO}.
--   $$
--   That is, the revenue-ordered strategy earns at least $\max_{1\le i\le k}N_ir_i$. This is inequality (6) of the paper, where $\mathrm{RO}$ is written as $\sum_{x\in S_j}\mathcal P(x,S_j)r(x)$ for an index $j$ of a best threshold set.
--
--   **Formalization Note** Optimality of $S^*$ is not needed and not assumed.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, proof of Theorem 3.3, inequality (6)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

namespace RevenueOrdered.PurchaseRatio

/-- Inequality (6) (arXiv:1606.01371v3, p. 9): for every set `S∗` and every `i ∈ [k]`,
`N_i r_i ≤ RO`, where `RO = max_{j ∈ [k]} rev(S_j)` is the revenue of the
revenue-ordered assortments strategy. Optimality of `S∗` is not needed. -/
theorem purchaseProfile_mul_level_le_roValue {C : Type*} [Fintype C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.roValue P r := by sorry

end RevenueOrdered.PurchaseRatio
