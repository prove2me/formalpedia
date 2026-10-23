-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_approx_greedy_bound
-- name    : RankAssort.SimpleLearn.approx_greedy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:23.985862+00:00
-- url     : https://prove2.me/theorems/69050f3b-3ad8-4f36-a123-ee6bdcbc7691
-- title:
--   Proof of Theorem 3, p. 58 — a ranking whose every rank is 2ϵ/n-approximately best satisfies E[H(π∗)] ≤ 2E[H(π̃)] + 2ϵ
-- statement:
--   Let types be drawn from $\mathcal D$ with a measurable type map, let $\epsilon$ be a real number, and let $\tilde\pi$ be a ranking of the $n$ products that satisfies (23) at every rank: for each $r \in [n]$, the product $\tilde\pi^{-1}(r)$ is $2\epsilon/n$-approximately best among the products not in $[\tilde\pi]_{r-1}$,
--
--   $$
--   \mathbb E[H([\tilde\pi]_{r-1}\cup \tilde\pi^{-1}(r))] - \mathbb E[H([\tilde\pi]_{r-1})] \ \ge\ \max_{i \notin [\tilde\pi]_{r-1}} \Bigl(\mathbb E[H([\tilde\pi]_{r-1}\cup i)] - \mathbb E[H([\tilde\pi]_{r-1})]\Bigr) - \frac{2\epsilon}{n}.
--   $$
--
--   Then for every ranking $\pi^*$,
--
--   $$
--   \mathbb E[H(\pi^*)] \le 2\,\mathbb E[H(\tilde\pi)] + 2\epsilon .
--   $$
--
--   This is the deterministic core of Theorem 3: "for any such fixed ranking $\tilde\pi$, we aim to show that $\mathbb E[H(\tilde\pi)] \ge \frac12\mathbb E[H(\pi^*)] - \epsilon$, or equivalently, $\mathbb E[H(\pi^*)] \le 2\mathbb E[H(\tilde\pi)] + 2\epsilon$" (p. 58), proved through (25)–(28). With $\epsilon = 0$ it contains the ½-approximation of the greedy ranking (Theorem 1).
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The hypothesis is written with `IsApproxBest`, i.e. with marginal benefits; by the second part of (6) (milestone `eq_6`) the two sides of (23), $\mathbb E[\bar C(r-1,\tilde\pi)C_{\tilde\pi^{-1}(r)}(\tilde\pi)]$ and $\mathbb E[\bar C(r-1,\tilde\pi)C_i([\tilde\pi]_{r-1}\cup i)]$, are exactly these marginal benefits. The maximum is over the unranked products, as in Algorithm 2; under the coupled law every term of (23) is nonnegative and an already-ranked product's term is $0$, so the two maxima agree. The tolerance $2\epsilon/n$ is a real division by $n$.
--
--   Differences from the source:
--   - generalization: ϵ > 0 (input of Algorithm 2) → any real eps; reason: the case ϵ > 0 is included
--   - generalization: π∗ the optimal ranking → every ranking π∗; reason: the optimal ranking is one instance
--   - reading: (23): max over i ∈ [n] of E[C̄(r − 1, π̃) Cᵢ([π̃]ᵣ₋₁ ∪ i)] → maximum over products i not in [π̃]ᵣ₋₁ (IsApproxBest); reason: [π̃]ᵣ₋₁ ∪ i is not a ranking when i is already ranked, and Algorithm 2 runs ALG on the unranked products U; under the model an already-ranked product's term is 0 and every term is ≥ 0, so the two maxima agree
--   - encoding: the two sides of (23), E[C̄(r − 1, π̃) C(·)] → marginal benefits margBenefit (difference of expected hooks); reason: equal by part 2 of (6) (milestone eq_6)
--   - encoding: expectation over the type (p, f, k) ∼ D, a random variable → integral over θ ∼ D of a function of τ θ, with TypeMeasurable τ (every coordinate of the type map measurable); reason: the expectations are undefined otherwise (Lean would return the junk value 0); the integrands lie in [0, 1], so measurability is all that is needed
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 58, proof of Theorem 3, 'Specifically, let us fix the ranking π̃ …', proved by (25)–(28), pp. 58–60

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem approx_greedy_bound {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ) (eps : ℝ)
    (piT : List (Fin n)) (hT : piT.Nodup) (hTlen : piT.length = n)
    (hgood : ∀ r < n, ∃ i, piT[r]? = some i ∧ IsApproxBest D τ (piT.take r) i (2 * eps / n))
    (piStar : List (Fin n)) (hs : piStar.Nodup) (hslen : piStar.length = n) :
    expHook D τ piStar ≤ 2 * expHook D τ piT + 2 * eps := by sorry
end RankAssort.SimpleLearn
