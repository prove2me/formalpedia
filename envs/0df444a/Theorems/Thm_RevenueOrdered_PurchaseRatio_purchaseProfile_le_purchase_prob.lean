-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_purchaseProfile_le_purchase_prob
-- name    : RevenueOrdered.PurchaseRatio.purchaseProfile_le_purchase_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:04:48.734898+00:00
-- url     : https://prove2.me/theorems/d9e70560-a6f3-4653-a66d-e38da55e35d4
-- title:
--   Proof of Theorem 3.3, p. 9 — N_i ≤ ∑_{x∈S_i} 𝒫(x, S_i) and N_i r_i ≤ ∑_{x∈S_i} 𝒫(x, S_i) r_i
-- statement:
--   Fix a regular discrete choice model $\mathcal P$ and a revenue function $r>0$ with distinct values $r_1<\dots<r_k$ and threshold sets $S_i=\{x: r(x)\ge r_i\}$. Let $S^*\subseteq\mathcal C$ be any assortment with purchase profile $N_i=\sum_{x\in S^*,\,r(x)\ge r_i}\mathcal P(x,S^*)$. Then for every $i\in[k]$
--   $$
--   N_i\le\sum_{x\in S_i}\mathcal P(x,S_i)
--   \qquad\text{and}\qquad
--   N_i\,r_i\le\sum_{x\in S_i}\mathcal P(x,S_i)\,r_i .
--   $$
--   In words, the probability that $S^*$ sells a product of revenue at least $r_i$ is at most the probability that $S_i$ sells anything. This is the first observation of the proof of Theorem 3.3.
--
--   **Formalization Note** The paper takes $S^*$ optimal; the observation holds for every $S^*$, and is stated so.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, proof of Theorem 3.3 (first observation)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

namespace RevenueOrdered.PurchaseRatio

/-- Proof of Theorem 3.3 (arXiv:1606.01371v3, p. 9, first observation): for every set `S∗`
and every `i ∈ [k]`, `N_i ≤ ∑_{x ∈ S_i} 𝒫(x, S_i)`, and hence
`N_i r_i ≤ ∑_{x ∈ S_i} 𝒫(x, S_i) r_i`. Optimality of `S∗` is not needed. -/
theorem purchaseProfile_le_purchase_prob {C : Type*} [Fintype C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i ≤ ∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i) ∧
      purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤ ∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i) * RevenueOrdered.Ratio.level r i := by sorry

end RevenueOrdered.PurchaseRatio
