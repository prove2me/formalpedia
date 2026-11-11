-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_A_1
-- name    : PostedPriceLimits.FullRevelation.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:02.788782+00:00
-- url     : https://prove2.me/theorems/2f2ac114-ec14-4b67-8c6d-7158cd8b78ff
-- title:
--   Lemma A.1 — $|\mathcal A_{t,L}|\le2^\lambda$
-- statement:
--   In the construction of §5 (for all sufficiently large $n$), for every realisation of the randomness, every block $t\in[n]$ and every name set $L\subseteq[\eta]$ with $|L|\le n$, the set $\mathcal A_{t,L}$ of grid functions $A:[\kappa]\times Z_t\to\{0,\varepsilon,2\varepsilon,\dots,1\}$ whose sections $A(k,\cdot)$ are $\mathcal P_{t,L}$-measurable satisfies
--   $$|\mathcal A_{t,L}|\le2^\lambda.$$
--
--   The bound is used for union bounds over all clauses of the non-owner valuations in Appendix A and Lemma 5.15.
--
--   **Formalization Note** $\mathcal A_{t,L}$ is a set of functions vanishing off $[\kappa]\times Z_t$; its cardinality is the extended cardinal `encard`, which is $\infty$ for infinite sets.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: functions A : [κ] × Z_t → grid → functions ℕ → Z_t → ℝ that vanish off [κ] × Z_t; reason: bijective with the source's set, so the cardinality is unchanged
--   - generalization: the sampled construction with injective names, a permutation and uniform labels in [0,1] → every latent point, without IsRealisation; reason: the bound uses only the finite range of ψ′ and the grid size, which hold at every latent point; every source realization is included
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma A.1, p.28 (PDF 29); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction

namespace PostedPriceLimits.FullRevelation

/-- Lemma A.1 (for all sufficiently large `n`). `|𝒜_{t,L}| ≤ 2^λ` for every block `t`, every
`L ⊆ [η]` with `|L| ≤ n`, and every realisation of the randomness. -/
theorem lemma_A_1 : ∃ N : ℕ, ∀ n ≥ N, ∀ (ω : Latent n) (t : Fin n)
    (L : Finset (Fin (poolSize n))), L.card ≤ n →
      (gridFns ω t L).encard ≤ ((2 ^ lam n : ℕ) : ℕ∞) := by sorry

end PostedPriceLimits.FullRevelation
