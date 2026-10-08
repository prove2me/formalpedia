-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_purchase_prob_mono
-- name    : RevenueOrdered.Nesting.purchase_prob_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:06:35.107922+00:00
-- url     : https://prove2.me/theorems/2bc90b5c-8cdd-4780-901b-21732a6a8cc2
-- title:
--   Lemma 2.1 — the purchase probability does not decrease when the choice set is enlarged
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of a regular discrete choice model on the products $\mathcal C$. Then for every $S\subseteq S'\subseteq\mathcal C$,
--   $$
--   \sum_{x\in S}\mathcal P(x,S)\le\sum_{x\in S'}\mathcal P(x,S').
--   $$
--
--   In words, the probability that the consumer makes some purchase does not decrease when the choice set is enlarged. In the proof of Theorem 5.1 it is what makes the lowest optimal revenue-ordered index move monotonically with a uniform shift of the revenues (Lemma .1).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_Model

namespace RevenueOrdered.Nesting

/-- Lemma 2.1 (Berbeglia–Joret, arXiv:1606.01371v3, p. 6): under a regular discrete choice
model the probability of making a purchase does not decrease when the choice set is enlarged,
`∑_{x ∈ S} 𝒫(x, S) ≤ ∑_{x ∈ S'} 𝒫(x, S')` for `S ⊆ S'`. -/
theorem purchase_prob_mono {C : Type*} {P : C → Finset C → ℝ} (hP : IsRegular P)
    {S S' : Finset C} (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by sorry

end RevenueOrdered.Nesting
