-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_eq_6
-- name    : RankAssort.SimpleLearn.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:37.805327+00:00
-- url     : https://prove2.me/theorems/d57d0b2a-1d97-496f-8935-cd157b6428b7
-- title:
--   (6), p. 50 — E[H(π)] is the sum over ranks of E[C̄(r − 1, π) C_{π⁻¹(r)}(π)], each term being a marginal benefit
-- statement:
--   Let types be drawn from $\mathcal D$ with a measurable type map. Then:
--
--   1. for every duplicate-free list $\pi$ of products, the expected hook decomposes over ranks as
--   $$
--   \mathbb E[H(\pi)] = \sum_{r=1}^{|\pi|} \mathbb E\bigl[\bar C(r-1,\pi)\, C_{\pi^{-1}(r)}(\pi)\bigr];
--   $$
--   2. term by term, for every prefix $\sigma$ and product $i$ such that $\sigma \cup i$ has no duplicates,
--   $$
--   \mathbb E\bigl[\bar C(|\sigma|,\sigma\cup i)\, C_{i}(\sigma \cup i)\bigr] = \mathbb E[H(\sigma\cup i)] - \mathbb E[H(\sigma)],
--   $$
--   i.e. the $r$-th term of (6) is the marginal benefit of the product at rank $r$ given the first $r-1$ (the interpretation of the marginal benefit on p. 16: "the probability that the customer clicks on the product at rank $r$ but not on any products in ranks $\{1,\dots,r-1\}$").
--
--   The paper states part 1 for full rankings; it is the telescoping identity used in the proofs of Theorems 1 and 3. Part 2 is the reading of its first equality that the proof of Theorem 3 uses to compare (23) with (6).
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The terms are `firstClickTerm D τ l r` for $r = 0,\dots,|l|-1$ (the paper's $r-1$), computed under the coupled first-click law; `margBenefit D τ σ i` is $\mathbb E[H(\sigma\cup i)] - \mathbb E[H(\sigma)]$. Measurability of the type map is assumed so that the expectations are genuine integrals.
--
--   Differences from the source:
--   - generalization: (6) for a ranking π of the n products → part 1 for every duplicate-free list l, the sum running over its length; reason: a full ranking is the case length l = n
--   - reading: the first equality of (6), read with the p. 16 interpretation of the marginal benefit → part 2: the r-th term with σ = the first r − 1 products equals E[H(σ ∪ i)] − E[H(σ)]; reason: this is the termwise reading the proof of Theorem 3 uses to compare (23) with (6)
--   - encoding: the C̄(r − 1, ·) C(·) expectations of the paper, on the customer's click realisation → computed under the coupled first-click law (one Bernoulli(pᵢ) like-coin per product, p. 53); reason: the paper evaluates these terms through this coupling (proof of Lemma 1, p. 53); milestone first_click_identity ties the coupled law to the sequential click law with bias
--   - encoding: expectation over the type (p, f, k) ∼ D, a random variable → integral over θ ∼ D of a function of τ θ, with TypeMeasurable τ (every coordinate of the type map measurable); reason: the expectations are undefined otherwise (Lean would return the junk value 0); the integrands lie in [0, 1], so measurability is all that is needed
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 50, (6); p. 16, interpretation of the marginal benefit

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem eq_6 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) [IsProbabilityMeasure D]
    (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) :
    (∀ l : List (Fin n), l.Nodup →
        expHook D τ l = ∑ r ∈ Finset.range l.length, firstClickTerm D τ l r) ∧
      (∀ (σ : List (Fin n)) (i : Fin n), (σ ++ [i]).Nodup →
        firstClickTerm D τ (σ ++ [i]) σ.length = margBenefit D τ σ i) := by sorry
end RankAssort.SimpleLearn
