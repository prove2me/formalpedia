-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_revenue_eq_profile_sum
-- name    : RevenueOrdered.PurchaseRatio.revenue_eq_profile_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:09.300229+00:00
-- url     : https://prove2.me/theorems/877a7ecb-2e13-49c6-8de6-a7297fb196e7
-- title:
--   Proof of Theorem 3.3, p. 9 — rev(S∗) = ∑_{i=1}^{ℓ} (N_i − N_{i+1}) r_i = ∑_{i=1}^{ℓ} (N_i − N_{i+1})/N_i · N_i r_i
-- statement:
--   Fix a regular discrete choice model $\mathcal P$ and a revenue function $r>0$ with distinct values $r_1<\dots<r_k$. Let $S^*\subseteq\mathcal C$ be an assortment with purchase profile $N_1,\dots,N_k$ and $N_{k+1}:=0$, and let $\ell\in[k]$ be maximum such that $N_\ell>0$. Then
--   $$
--   \sum_{x\in S^*}\mathcal P(x,S^*)\,r(x)
--   =\sum_{i=1}^{\ell}(N_i-N_{i+1})\,r_i
--   =\sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\,N_i r_i .
--   $$
--   The revenue of $S^*$ is thus a combination of the quantities $N_ir_i$ with the weights $(N_i-N_{i+1})/N_i$; this is the identity behind Theorem 3.3.
--
--   **Formalization Note** The hypotheses on $\ell$ are $1\le\ell\le k$, $N_\ell>0$, and $N_i\not>0$ for $\ell<i\le k$. The division in the second sum is by $N_i>0$ for $i\le\ell$, because $N$ is non-increasing. Optimality of $S^*$ is not needed and not assumed.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, proof of Theorem 3.3 (display expressing the revenue of S∗)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

namespace RevenueOrdered.PurchaseRatio

/-- The revenue of `S∗` in terms of its purchase profile (proof of Theorem 3.3,
arXiv:1606.01371v3, p. 9, display): if `ℓ ∈ [k]` is maximum with `N_ℓ > 0`, then
`rev(S∗) = ∑_{i=1}^{ℓ} (N_i − N_{i+1}) r_i = ∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i · N_i r_i`,
with `N_{k+1} = 0` (built into `purchaseProfile`). Optimality of `S∗` is not needed. -/
theorem revenue_eq_profile_sum {C : Type*} [Fintype C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ RevenueOrdered.Ratio.numVals r)
    (hℓpos : 0 < purchaseProfile P r S ℓ)
    (hℓmax : ∀ i, ℓ < i → i ≤ RevenueOrdered.Ratio.numVals r → ¬ 0 < purchaseProfile P r S i) :
    RevenueOrdered.Ratio.revenue P r S =
        ∑ i ∈ Finset.Icc 1 ℓ,
          (purchaseProfile P r S i - purchaseProfile P r S (i + 1)) * RevenueOrdered.Ratio.level r i ∧
      RevenueOrdered.Ratio.revenue P r S =
        ∑ i ∈ Finset.Icc 1 ℓ,
          (purchaseProfile P r S i - purchaseProfile P r S (i + 1)) / purchaseProfile P r S i *
            (purchaseProfile P r S i * RevenueOrdered.Ratio.level r i) := by sorry

end RevenueOrdered.PurchaseRatio
