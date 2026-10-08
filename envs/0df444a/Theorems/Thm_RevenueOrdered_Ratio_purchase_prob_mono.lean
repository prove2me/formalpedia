-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_purchase_prob_mono
-- name    : RevenueOrdered.Ratio.purchase_prob_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:05.002541+00:00
-- url     : https://prove2.me/theorems/3d455b57-30c5-4358-aaa8-a51dec29660f
-- title:
--   Lemma 2.1 — the purchase probability is monotone in the choice set
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of a regular discrete choice model on the products $\mathcal C$. Then for every $S\subseteq S'\subseteq\mathcal C$,
--   $$
--   \sum_{x\in S}\mathcal P(x,S)\;\le\;\sum_{x\in S'}\mathcal P(x,S').
--   $$
--
--   In words, the probability that the consumer buys something does not decrease when the choice set is enlarged. The paper calls this observation straightforward but important: it is the step at which the no-purchase case of the regularity axiom enters every approximation bound.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace RevenueOrdered.Ratio

/-- Lemma 2.1 (p. 6): under a regular discrete choice model the probability of making a
purchase does not decrease when the choice set is enlarged. -/
theorem purchase_prob_mono {C : Type*} (P : C → Finset C → ℝ) (hP : IsRegular P)
    (S S' : Finset C) (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by sorry

end RevenueOrdered.Ratio
