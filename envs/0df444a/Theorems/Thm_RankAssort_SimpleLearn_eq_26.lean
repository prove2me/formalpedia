-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_eq_26
-- name    : RankAssort.SimpleLearn.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:39.984357+00:00
-- url     : https://prove2.me/theorems/b1669d5b-eede-47d3-878d-9f3ff38c0a92
-- title:
--   (26), p. 59 — the joint no-click/click term is at most the marginal benefit of π∗'s r-th product placed after [π̃]ᵣ₋₁
-- statement:
--   Let types be drawn from $\mathcal D$ with a measurable type map, let $\tilde\pi$ and $\pi^*$ be rankings of the $n$ products, fix a rank $r \in [n]$ and let $i^* = \pi^{*-1}(r)$. Then
--
--   $$
--   \mathbb E\bigl[\bar C(r-1,\tilde\pi)\,\bar C(r-1,\pi^*)\,C_{i^*}(\pi^*)\bigr] \le \mathbb E\bigl[\bar C(r-1,\tilde\pi)\,C_{i^*}([\tilde\pi]_{r-1}\cup i^*)\bigr],
--   $$
--
--   where $[\tilde\pi]_{r-1}\cup i^*$ is the prefix of the first $r-1$ products of $\tilde\pi$ followed by $i^*$ at rank $r$. When $i^*$ already appears among the first $r-1$ products of $\tilde\pi$, both sides are $0$ (footnote 17).
--
--   This is the argument of Lemma 1 applied to the learned ranking $\tilde\pi$; combined with (23) it bounds each term of (25) by the corresponding term of (6) plus $2\epsilon/n$.
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The left side is `jointTerm D τ piT piStar r`, the right side `firstClickTerm D τ (piT.take r ++ [iStar]) r` with 0-based $r$; both are computed under the coupled first-click law. The statement holds for every ranking $\tilde\pi$, not only for the output of Algorithm 2.
--
--   Differences from the source:
--   - generalization: π̃ the ranking returned by Algorithm 2 satisfying (24), π∗ the optimal ranking → π̃ and π∗ any two rankings; reason: the argument uses neither property; the paper's pair is one instance
--   - encoding: i∗ = π∗⁻¹(r) → iStar with piStar[r]? = some iStar (0-based r); reason: the same product
--   - encoding: the C̄(r − 1, ·) C(·) expectations of the paper, on the customer's click realisation → computed under the coupled first-click law (one Bernoulli(pᵢ) like-coin per product, p. 53); reason: the paper evaluates these terms through this coupling (proof of Lemma 1, p. 53); milestone first_click_identity ties the coupled law to the sequential click law with bias
--   - encoding: expectation over the type (p, f, k) ∼ D, a random variable → integral over θ ∼ D of a function of τ θ, with TypeMeasurable τ (every coordinate of the type map measurable); reason: the expectations are undefined otherwise (Lean would return the junk value 0); the integrands lie in [0, 1], so measurability is all that is needed
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 59, (26), proof of Theorem 3, with footnote 17

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem eq_26 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (piT piStar : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length = n)
    (hs : piStar.Nodup) (hslen : piStar.length = n)
    (r : ℕ) (hr : r < n) (iStar : Fin n) (hiStar : piStar[r]? = some iStar) :
    jointTerm D τ piT piStar r ≤ firstClickTerm D τ (piT.take r ++ [iStar]) r := by sorry
end RankAssort.SimpleLearn
