-- Prove2me | Theorems.Thm_RevenueOrdered_PurchaseRatio_purchase_prob_mono
-- name    : RevenueOrdered.PurchaseRatio.purchase_prob_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:51.412757+00:00
-- url     : https://prove2.me/theorems/a1b29522-07fa-4bdd-9fe4-915f54cebe6d
-- title:
--   Lemma 2.1 — the purchase probability does not decrease when the choice set is enlarged
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of a regular discrete choice model on a product set $\mathcal C$. Then for all choice sets $S\subseteq S'\subseteq\mathcal C$,
--   $$
--   \sum_{x\in S}\mathcal P(x,S)\;\le\;\sum_{x\in S'}\mathcal P(x,S').
--   $$
--   The probability that a consumer buys something is monotone in the offered set. This is the property of regular models on which every revenue bound of the paper rests.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace RevenueOrdered.PurchaseRatio

/-- Lemma 2.1 (Berbeglia–Joret, arXiv:1606.01371v3, p. 6): under a regular discrete choice
model the probability of making a purchase does not decrease when the choice set is enlarged:
`∑_{x ∈ S} 𝒫(x, S) ≤ ∑_{x ∈ S'} 𝒫(x, S')` for every `S ⊆ S' ⊆ 𝒞`. -/
theorem purchase_prob_mono {C : Type*} (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P)
    (S S' : Finset C) (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by sorry

end RevenueOrdered.PurchaseRatio
