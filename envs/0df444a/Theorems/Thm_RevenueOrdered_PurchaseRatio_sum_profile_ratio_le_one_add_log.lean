-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_sum_profile_ratio_le_one_add_log
-- name    : RevenueOrdered.PurchaseRatio.sum_profile_ratio_le_one_add_log
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:56.691056+00:00
-- url     : https://prove2.me/theorems/3f1d20f0-0627-4ba0-aaf1-5a680aabc2c1
-- title:
--   Proof of Theorem 3.3, p. 9 (last inequality) — ∑_{i=1}^{ℓ} (N_i − N_{i+1})/N_i ≤ 1 + ln(N_1/N_ℓ)
-- statement:
--   Let $\ell\ge1$ and let $N_1\ge N_2\ge\dots\ge N_\ell>0$ be real numbers, with $N_{\ell+1}=0$. Then
--   $$
--   \sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\;\le\;1+\ln\frac{N_1}{N_\ell}.
--   $$
--   In the proof of Theorem 3.3 this is applied to the purchase profile of an optimal assortment, with $\nu=N_1/N_\ell\ge1$, and turns the sum form of the approximation factor into the factor $1/(1+\ln\nu)$. The paper states this step without proof.
--
--   **Formalization Note** The paper writes this step multiplied by the revenue-ordered value $\sum_{x\in S_j}\mathcal P(x,S_j)r(x)\ge0$; the statement here is the inequality between the two factors, for an arbitrary sequence $N$ indexed by natural numbers.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, Theorem 3.3 (the comparison 1/∑ ⩾ 1/(1 + ln ν)) and the last inequality of its proof

import Mathlib

namespace RevenueOrdered.PurchaseRatio

/-- The logarithmic step of the proof of Theorem 3.3 (arXiv:1606.01371v3, p. 9, last
inequality), stated for an arbitrary sequence: if `N_1 ≥ N_2 ≥ ⋯ ≥ N_ℓ > 0` and
`N_{ℓ+1} = 0`, then `∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i ≤ 1 + ln(N_1 / N_ℓ)`. -/
theorem sum_profile_ratio_le_one_add_log (N : ℕ → ℝ) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ)
    (hanti : ∀ i, 1 ≤ i → i < ℓ → N (i + 1) ≤ N i) (hℓpos : 0 < N ℓ) (hsucc : N (ℓ + 1) = 0) :
    ∑ i ∈ Finset.Icc 1 ℓ, (N i - N (i + 1)) / N i ≤ 1 + Real.log (N 1 / N ℓ) := by sorry

end RevenueOrdered.PurchaseRatio
