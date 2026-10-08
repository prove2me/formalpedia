-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_revenue_ordered_purchase_ratio_bound
-- name    : RevenueOrdered.PurchaseRatio.revenue_ordered_purchase_ratio_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:21.914193+00:00
-- url     : https://prove2.me/theorems/fd2f4bf9-3480-4019-af0a-149fd1d93947
-- title:
--   Theorem 3.3 — revenue-ordered assortments earn OPT/∑_{i≤ℓ}(N_i − N_{i+1})/N_i ≥ OPT/(1 + ln ν)
-- statement:
--   Fix a regular discrete choice model $\mathcal P$ on a nonempty finite product set $\mathcal C$ and a revenue function $r:\mathcal C\to\mathbb R_{>0}$ with distinct values $r_1<\dots<r_k$. Let $\mathrm{RO}=\max_{1\le i\le k}\mathrm{rev}(S_i)$ be the revenue of the revenue-ordered assortments strategy and $\mathrm{OPT}$ the optimum revenue. Let $S^*\subseteq\mathcal C$ be an optimal assortment, $\mathrm{rev}(S^*)=\mathrm{OPT}$, and let
--   $$
--   N_i=\sum_{\substack{x\in S^*\\ r(x)\ge r_i}}\mathcal P(x,S^*)\qquad(i\in[k]),\qquad N_{k+1}:=0 .
--   $$
--   Suppose $N_1>0$ and let $\ell\in[k]$ be maximum such that $N_\ell>0$. Then
--   $$
--   \mathrm{OPT}\;\le\;\Big(\sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\Big)\,\mathrm{RO}
--   \qquad\text{and}\qquad
--   \sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\;\le\;1+\ln\nu,\quad \nu=\frac{N_1}{N_\ell}.
--   $$
--   Equivalently, revenue-ordered assortments approximate the optimum revenue within a factor $1/\sum_{i=1}^{\ell}(N_i-N_{i+1})/N_i\ge 1/(1+\ln\nu)$. The bound depends on how the purchase probability of an optimal assortment is spread over revenue levels, not on the revenues themselves, and is incomparable with the bound $1/(1+\ln(r_k/r_1))$ of Theorem 3.2.
--
--   **Formalization Note** The approximation factor is stated in product form, $\mathrm{OPT}\le D\cdot\mathrm{RO}$ with $D$ the sum, rather than as a ratio. Indices are 1-based natural numbers; $N_{k+1}=0$ is built into the definition of the profile. "$\ell$ maximum with $N_\ell>0$" is encoded as $1\le\ell\le k$, $N_\ell>0$ and $N_i\not>0$ for $\ell<i\le k$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, Theorem 3.3

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

namespace RevenueOrdered.PurchaseRatio

/-- Theorem 3.3 (Berbeglia–Joret, arXiv:1606.01371v3, p. 9). Let `S∗` be an optimal
assortment, `N_i = ∑_{x ∈ S∗, r(x) ≥ r_i} 𝒫(x, S∗)` for `i ∈ [k]`, suppose `N_1 > 0`, and
let `ℓ ∈ [k]` be maximum with `N_ℓ > 0`. Then revenue-ordered assortments approximate the
optimum within the factor `1 / ∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i ≥ 1 / (1 + ln ν)`,
`ν = N_1 / N_ℓ`; stated in product form:
`OPT ≤ (∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i) · RO` and
`∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i ≤ 1 + ln(N_1 / N_ℓ)`. -/
theorem revenue_ordered_purchase_ratio_bound {C : Type*} [Fintype C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (hSopt : RevenueOrdered.Ratio.revenue P r S = RevenueOrdered.Ratio.opt P r)
    (hN1 : 0 < purchaseProfile P r S 1)
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ RevenueOrdered.Ratio.numVals r)
    (hℓpos : 0 < purchaseProfile P r S ℓ)
    (hℓmax : ∀ i, ℓ < i → i ≤ RevenueOrdered.Ratio.numVals r → ¬ 0 < purchaseProfile P r S i) :
    RevenueOrdered.Ratio.opt P r ≤ purchaseRatioSum P r S ℓ * RevenueOrdered.Ratio.roValue P r ∧
      purchaseRatioSum P r S ℓ ≤
        1 + Real.log (purchaseProfile P r S 1 / purchaseProfile P r S ℓ) := by sorry

end RevenueOrdered.PurchaseRatio
