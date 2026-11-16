-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_lemma_6_1
-- name    : PooledTestingAdaptivity.Gap.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:38:02.336955+00:00
-- url     : https://prove2.me/theorems/10c7f324-ef53-478a-a5d4-f25a7a3a2c70
-- title:
--   Lemma 6.1 — Posterior domination
-- statement:
--   Let $J$ be a pooled-testing instance with independent health bits $X_i\sim\mathrm{Bernoulli}(q_i)$. Let $H$ be any history of tested pools and outcomes with positive probability $P(H)>0$, and let $C(H)$ be the union of its negative pools. For every set $A\subseteq[n]\setminus C(H)$,
--   $$P(X_A=1\mid H)\le\prod_{i\in A}q_i .$$
--
--   The posterior probability that a set of uncleared individuals is all healthy never exceeds its prior probability, although individual posterior marginals may increase. The bound controls conditional gains in the proofs of Lemma 6.2, Theorem 3.8, Theorem 3.9 and Theorem 7.2.
--
--   Differences from the source:
--   - encoding: population [n], a history as a sequence of pools and outcomes → Fin n, a list of nonempty finsets with a Boolean outcome (true = negative); reason: reindexing; the same histories
--   - encoding: the conditional probability P(X_A = 1 | H) → the ratio of the product-prior masses of consistent profiles with x_A = 1 and of all consistent profiles; reason: definition of conditional probability on a finite space with P(H) > 0
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Lemma 6.1, printed p. 20, PDF p. 21

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Lemma 6.1 (Posterior domination), printed p. 20, PDF p. 21. -/
theorem lemma_6_1 {n : ℕ} (J : Instance n) (H : History n) (hH : 0 < histMass J H)
    (A : Finset (Fin n)) (hA : Disjoint A (histCleared H)) :
    condHealthy J H A ≤ ∏ i ∈ A, J.q i := by sorry

end PooledTestingAdaptivity.Gap.Supplement
