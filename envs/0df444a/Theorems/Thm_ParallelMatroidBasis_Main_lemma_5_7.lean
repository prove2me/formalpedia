-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_lemma_5_7
-- name    : ParallelMatroidBasis.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:47.226277+00:00
-- url     : https://prove2.me/theorems/912b58b5-fd9f-43d6-88b3-09e3866f719d
-- title:
--   Lemma 5.7 (deterministic form) — $O(1+\log\log n+\sqrt{2^\ell}/\log n)$ peeled sets of size in $[2^\ell,2^{\ell+1})$
-- statement:
--   There are absolute constants $C>0$ and $n_0$ such that the following holds for every $n\ge n_0$. Let $M$ be a matroid and $S_1,\dots,S_k$ finite sets such that
--   1. $\alpha(S_i)\ge 50$ for every $i\in[k]$;
--   2. $\alpha(S_i)/|S_i|\le 1/(100\log_2 n)$ for every $i<k$;
--   3. for all $i<j<k$ with $|S_i|\le 2|S_j|$,
--   $$\alpha(S_j)\ \ge\ \frac{\alpha(S_i)|S_j|}{|S_i|}+\sqrt{\frac{\alpha(S_i)|S_j|}{|S_i|}\cdot\frac{\log_2 n}{16}}$$
--   (the conclusion of Claim 5.6).
--
--   Then for every integer $\ell\in[\lfloor\log_2 n\rfloor]$, the number $\gamma=|\{i\in[k]:|S_i|\in[2^\ell,2^{\ell+1}-1]\}|$ satisfies
--   $$\gamma\ \le\ C\Big(1+\log_2\log_2 n+\frac{\sqrt{2^\ell}}{\log_2 n}\Big).$$
--
--   In the paper $S_1,\dots,S_k$ are the sets peeled off by Algorithm 2 (the last index $k$ may violate the stopping test and is counted in $\gamma$). Summing over $\ell$ gives the bound on the number of peeled sets (Lemma 5.8).
--
--   **Formalization Note.** $[k]=\{1,\dots,k\}$ and $\lfloor\log_2 n\rfloor$ is `Nat.log 2 n`. The O-constant is an existential $C$ chosen before $n$, the matroid and the sets; by hypothesis 1 every $S_i$ is dependent.
--
--   Differences from the source:
--   - generalization: with probability ≥ 1 − 2n·2^{−n}, for the sets S_1, …, S_k peeled off by Algorithm 2 from a matroid with at most n elements → for every matroid and every finite sets S_1, …, S_k satisfying α(S_i) ≥ 50 (i ∈ [k]), α(S_i)/|S_i| ≤ 1/(100 log₂ n) (i < k) and the conclusion of Claim 5.6 (i < j < k, |S_i| ≤ 2|S_j|), with no bound on the ground set (deterministic); reason: the paper proves these properties of the sets peeled off by Algorithm 2 hold on its good event of probability ≥ 1 − 2n·2^{−n} (Claim 5.1 and the EstimateAlpha bound (4), pp.16–19, and the preprocessing α ≥ 50), and its proof then uses only them; Algorithm 2 calls RemoveSmallCircuits and EstimateAlpha from [KPS25], which the paper does not define, so the probabilistic wording cannot be formalized from this source. The Lean statement holds for every family of sets with these properties, in particular for the peeled sets on the good event, so it specializes to the source's claim there; the proof uses no ground-set bound, so none is assumed
--   - encoding: γ = O(1 + log log n + √(2^ℓ)/log n), for sufficiently large n → ∃ C > 0, ∃ n₀, ∀ n ≥ n₀, γ ≤ C(1 + log₂ log₂ n + √(2^ℓ)/log₂ n); reason: an O-bound is an absolute constant, quantified before the instance
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma 5.7 and its proof, pp.20–21 (PDF pp.22–23); properties of the peeled sets, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_CircuitStats

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Lemma 5.7, PDF p.22 (printed p.20), in the deterministic form its proof establishes on the
paper's good event. There are absolute constants `C > 0` and `n₀` such that for `n ≥ n₀`: if
`S_1, …, S_k` are finite sets in a matroid `M` with (c) `α(S_i) ≥ 50` for all `i ∈ [k]`,
(b) `α(S_i)/|S_i| ≤ 1/(100 log₂ n)` for all `i < k`, and (a) the conclusion of Claim 5.6 for all
`i < j < k` with `|S_i| ≤ 2|S_j|`, then for every integer `ℓ ∈ [⌊log₂ n⌋]` the number
`γ = |{i ∈ [k] : |S_i| ∈ [2^ℓ, 2^{ℓ+1} − 1]}|` satisfies
`γ ≤ C (1 + log₂ log₂ n + √(2^ℓ) / log₂ n)`. -/
theorem lemma_5_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (k : ℕ) (S : ℕ → Finset α),
        (∀ i, 1 ≤ i → i ≤ k → 50 ≤ alphaVal M (S i)) →
        (∀ i, 1 ≤ i → i < k →
          (alphaVal M (S i) : ℝ) / ((S i).card : ℝ) ≤ 1 / (100 * Real.logb 2 n)) →
        (∀ i j, 1 ≤ i → i < j → j < k → ((S i).card : ℝ) ≤ 2 * ((S j).card : ℝ) →
          (alphaVal M (S i) : ℝ) * (S j).card / (S i).card +
              Real.sqrt ((alphaVal M (S i) : ℝ) * (S j).card / (S i).card *
                Real.logb 2 n / 16) ≤
            (alphaVal M (S j) : ℝ)) →
        ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ Nat.log 2 n →
          (((Finset.Icc 1 k).filter
              (fun i => 2 ^ ℓ ≤ (S i).card ∧ (S i).card ≤ 2 ^ (ℓ + 1) - 1)).card : ℝ) ≤
            C * (1 + Real.logb 2 (Real.logb 2 n) +
              Real.sqrt ((2 : ℝ) ^ ℓ) / Real.logb 2 n) := by sorry

end ParallelMatroidBasis.Main
