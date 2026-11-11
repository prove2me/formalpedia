-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_lemma_5_8
-- name    : ParallelMatroidBasis.Main.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:51.260693+00:00
-- url     : https://prove2.me/theorems/23925646-7309-47fe-b8fe-fdc212f6960c
-- title:
--   Lemma 5.8 (deterministic form) — the decomposition has $k=O(n^{1/3}/\log^{2/3}n)$ sets
-- statement:
--   There are absolute constants $C>0$ and $n_0$ such that the following holds for every $n\ge n_0$. Let $M$ be a matroid and let $S_1,\dots,S_k$ be pairwise disjoint subsets of a set $E$ with $|E|\le n$ that satisfy hypotheses 1–3 of Lemma 5.7: $\alpha(S_i)\ge 50$ for all $i\in[k]$, $\alpha(S_i)/|S_i|\le 1/(100\log_2 n)$ for $i<k$, and the α-growth inequality of Claim 5.6 for $i<j<k$ with $|S_i|\le 2|S_j|$. Then
--   $$k\ \le\ C\,\frac{n^{1/3}}{(\log_2 n)^{2/3}} .$$
--
--   The peeling stage of the algorithm thus takes $O(n^{1/3}/\log^{2/3}n)$ rounds, which is the source of the $\log^{1/3}n$ improvement in the round complexity of the main algorithm.
--
--   **Formalization Note.** The O-constant is an existential $C$ chosen before $n$, the matroid and the sets. Disjointness and $|E|\le n$ are properties of the peeled sets (each $S_i$ is removed from the matroid before the next is chosen, p.18).
--
--   Differences from the source:
--   - generalization: with probability ≥ 1 − 2n·2^{−n}, for the sets S_1, …, S_k peeled off by Algorithm 2 from a matroid on n elements → for every matroid and pairwise disjoint S_1, …, S_k ⊆ E, |E| ≤ n, satisfying the hypotheses of Lemma 5.7 (deterministic); reason: the paper proves these properties of the sets peeled off by Algorithm 2 hold on its good event of probability ≥ 1 − 2n·2^{−n} (Claim 5.1 and the EstimateAlpha bound (4), pp.16–19, and the preprocessing α ≥ 50), and its proof then uses only them; Algorithm 2 calls RemoveSmallCircuits and EstimateAlpha from [KPS25], which the paper does not define, so the probabilistic wording cannot be formalized from this source. The Lean statement holds for every family of sets with these properties, in particular for the peeled sets on the good event, so it specializes to the source's claim there
--   - encoding: k = O(n^{1/3}/log^{2/3} n), for sufficiently large n → ∃ C > 0, ∃ n₀, ∀ n ≥ n₀, k ≤ C n^{1/3}/(log₂ n)^{2/3}; reason: an O-bound is an absolute constant, quantified before the instance
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma 5.8 and its proof, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_CircuitStats

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Lemma 5.8, PDF p.23 (printed p.21), in the deterministic form its proof establishes on the
paper's good event. There are absolute constants `C > 0` and `n₀` such that for `n ≥ n₀`: if
`S_1, …, S_k` are pairwise disjoint subsets of a set `E` with `|E| ≤ n` in a matroid `M`,
satisfying the hypotheses (a)–(c) of Lemma 5.7, then `k ≤ C · n^{1/3} / (log₂ n)^{2/3}`. -/
theorem lemma_5_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (E : Finset α) (k : ℕ) (S : ℕ → Finset α),
        E.card ≤ n →
        (∀ i, 1 ≤ i → i ≤ k → S i ⊆ E) →
        (∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j → Disjoint (S i) (S j)) →
        (∀ i, 1 ≤ i → i ≤ k → 50 ≤ alphaVal M (S i)) →
        (∀ i, 1 ≤ i → i < k →
          (alphaVal M (S i) : ℝ) / ((S i).card : ℝ) ≤ 1 / (100 * Real.logb 2 n)) →
        (∀ i j, 1 ≤ i → i < j → j < k → ((S i).card : ℝ) ≤ 2 * ((S j).card : ℝ) →
          (alphaVal M (S i) : ℝ) * (S j).card / (S i).card +
              Real.sqrt ((alphaVal M (S i) : ℝ) * (S j).card / (S i).card *
                Real.logb 2 n / 16) ≤
            (alphaVal M (S j) : ℝ)) →
        (k : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 3) / (Real.logb 2 n) ^ ((2 : ℝ) / 3) := by sorry

end ParallelMatroidBasis.Main
