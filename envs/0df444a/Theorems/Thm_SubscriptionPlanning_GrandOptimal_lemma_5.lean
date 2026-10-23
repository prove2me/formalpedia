-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_5
-- name    : SubscriptionPlanning.GrandOptimal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:03.191986+00:00
-- url     : https://prove2.me/theorems/730bdd21-d0b4-4dfe-8b82-aad7fef3da6c
-- title:
--   Lemma 5, pp. 21–22 (PDF 22–23), posed per user type — Rent(i, ∅, r) ≥ Rent(i, S, r) and SubGain(i, 𝓜, r) ≥ Rent(i, ∅, r) for r ≥ 0
-- statement:
--   Let user type $i$ face nonnegative rental prices $\mathbf r \ge 0$. For every subscription set $S \subseteq \mathcal M$:
--
--   1. $\mathrm{Rent}(i,\emptyset,\mathbf r) \ge \mathrm{Rent}(i,S,\mathbf r)$;
--   2. $\mathrm{SubGain}(i,\mathcal M,\mathbf r) \ge \mathrm{Rent}(i,\emptyset,\mathbf r)$.
--
--   Subscribing to more items can only lower the rental revenue, and the rental revenue of a non-subscriber never exceeds what she would gain by subscribing to everything. Both facts compare the subscription and rental channels in the proofs of Theorems 1 and 2.
--
--   **Formalization Note** The paper states the lemma inside the proof of Theorem 1 in the item-dependent setting; it is posed here for each user type. Part 1 relies on the per-watch choice using one fixed tie-break priority (outside option, then items by index), independent of $S$. The hypothesis $\mathbf r \ge 0$ is added.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), pp. 21–22, Lemma 5 (proof of Theorem 1)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem lemma_5 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω) (hM : M.Valid)
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (i : Fin n) (S : Finset (Fin m)) :
    rent M i S r ≤ rent M i ∅ r ∧ rent M i ∅ r ≤ subGain M i Finset.univ r := by sorry
end SubscriptionPlanning.GrandOptimal
