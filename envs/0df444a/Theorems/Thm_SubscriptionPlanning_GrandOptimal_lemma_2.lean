-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_2
-- name    : SubscriptionPlanning.GrandOptimal.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:10.798773+00:00
-- url     : https://prove2.me/theorems/081af573-dcfd-4d09-8753-8aeb05d55796
-- title:
--   Lemma 2, p. 10 (PDF 11), posed per user type — SubGain(i, 𝓜, r) ≥ SubGain(i, S, r) + Rent(i, S, r) for r ≥ 0
-- statement:
--   Let user type $i$ face nonnegative rental prices $\mathbf r \ge 0$. For every subscription set $S \subseteq \mathcal M$,
--   $$\mathrm{SubGain}(i,\mathcal M,\mathbf r) \ge \mathrm{SubGain}(i,S,\mathbf r) + \mathrm{Rent}(i,S,\mathbf r).$$
--
--   The sum of the subscription gain and the rental revenue from one watch is largest for the grand set: subscribing to everything leaves the user at least the utility she had plus what she paid in rent. This is the basic comparison behind every optimality statement about the grand subscription.
--
--   **Formalization Note** The paper states the lemma in §4, where values do not depend on the user type; it is posed here for each user type $i$, as the proof of Theorem 2 uses it. The hypothesis $\mathbf r \ge 0$ is added: Definition 1 allows any $\mathbf r \in \mathbb R^m$, and the inequality fails for negative rental prices.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 10, Lemma 2 (proof p. 21)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem lemma_2 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω) (hM : M.Valid)
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (i : Fin n) (S : Finset (Fin m)) :
    subGain M i S r + rent M i S r ≤ subGain M i Finset.univ r := by sorry
end SubscriptionPlanning.GrandOptimal
