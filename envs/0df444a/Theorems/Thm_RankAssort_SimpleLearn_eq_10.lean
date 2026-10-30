-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_eq_10
-- name    : RankAssort.SimpleLearn.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:41.939954+00:00
-- url     : https://prove2.me/theorems/c134ab0f-826a-4517-8cb9-7f5932c6ee06
-- title:
--   (10), p. 51 — E[H(π∗)] ≤ E[H(π)] + Σᵣ E[C̄(r − 1, π) C̄(r − 1, π∗) C_{π∗⁻¹(r)}(π∗)] for any rankings π, π∗
-- statement:
--   Let types be drawn from $\mathcal D$ with a measurable type map, and let $\pi$ and $\pi^*$ be any two rankings of the $n$ products. Then
--
--   $$
--   \mathbb E[H(\pi^*)] \le \mathbb E[H(\pi)] + \sum_{r=1}^{n} \mathbb E\bigl[\bar C(r-1,\pi)\,\bar C(r-1,\pi^*)\,C_{\pi^{*-1}(r)}(\pi^*)\bigr],
--   $$
--
--   where the joint terms are computed under the coupled first-click law, which puts the clicks of one customer under the two rankings on a common probability space.
--
--   This is the decomposition of the optimum in terms of an arbitrary ranking, proved in the proof of Theorem 1 and reused, with $\pi = \tilde\pi$, as (25) in the proof of Theorem 3.
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The joint terms are `jointTerm D τ l piStar r` for $r = 0,\dots,n-1$. The paper calls $\pi^*$ the optimal ranking; the inequality holds for every ranking $\pi^*$ and is stated so.
--
--   Differences from the source:
--   - generalization: π∗ the optimal ranking, π an arbitrary ranking → π and π∗ both arbitrary rankings; reason: the chain (7)–(10) never uses optimality of π∗; the optimal ranking is one instance
--   - encoding: the C̄(r − 1, ·) C(·) expectations of the paper, on the customer's click realisation → computed under the coupled first-click law (one Bernoulli(pᵢ) like-coin per product, p. 53); reason: the paper evaluates these terms through this coupling (proof of Lemma 1, p. 53); milestone first_click_identity ties the coupled law to the sequential click law with bias
--   - encoding: expectation over the type (p, f, k) ∼ D, a random variable → integral over θ ∼ D of a function of τ θ, with TypeMeasurable τ (every coordinate of the type map measurable); reason: the expectations are undefined otherwise (Lean would return the junk value 0); the integrands lie in [0, 1], so measurability is all that is needed
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 51, (7)–(10), proof of Theorem 1

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem eq_10 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (l piStar : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n)
    (hs : piStar.Nodup) (hslen : piStar.length = n) :
    expHook D τ piStar ≤ expHook D τ l + ∑ r ∈ Finset.range n, jointTerm D τ l piStar r := by sorry
end RankAssort.SimpleLearn
