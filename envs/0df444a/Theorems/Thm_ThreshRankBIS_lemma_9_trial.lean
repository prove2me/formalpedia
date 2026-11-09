-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_9_trial
-- name    : ThreshRankBIS.lemma_9_trial
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:57:13.504521+00:00
-- url     : https://prove2.me/theorems/59207f36-af94-4a9d-b1c7-5e016b461615
-- title:
--   Proof of Lemma 9 — one trial accepts $J$ with probability $\lambda^{|J|}/W_0$; $\Pr(Q>r)=(1-1/M)^r$
-- statement:
--   Let $I_1,\dots,I_M$ ($M\ge1$) be a list of finite sets, $\lambda>0$, $q=1+\lambda$, $W_0=\sum_jq^{|I_j|}$, $a(J)=|\{j:J\subseteq I_j\}|$, $\mathcal J=\bigcup_j2^{I_j}$ and $Z=\sum_{J\in\mathcal J}\lambda^{|J|}$. For one trial of the union sampler:
--
--   1. the proposal probability of $J$ is $a(J)\lambda^{|J|}/W_0$;
--   2. if $J\subseteq I_j$, the first index $\ell$ with $J\subseteq I_\ell$ in a stream of fresh uniform queries equals $j$ with probability $1/a(J)$;
--   3. a trial accepts $J$ with probability $\lambda^{|J|}/W_0$ for every $J\in\mathcal J$;
--   4. a trial accepts with total probability $Z/W_0$;
--   5. conditionally on acceptance the output is $J$ with probability $\lambda^{|J|}/Z$, the required distribution;
--   6. the total query count $Q$ of the run is geometric with mean $M$:
--   $$
--   \Pr(Q>r)=(1-1/M)^r\le e^{-r/M}\qquad(r\ge1).
--   $$
--
--   For clause 6: the queries are fresh uniform indices, independent of everything else, and the run terminates at a query exactly when its index equals the current source index $j$, which is determined by the history before that query.
--
--   This is the weighted-coverage step of Karp, Luby and Madras with which the covered family is counted and sampled without overcounting.
--
--   Differences from the source:
--   - generalization: a nonempty list I₁, …, I_M of independent sets of G → a nonempty list of arbitrary finite sets of any type with decidable equality; reason: the argument never uses independence; the paper's list is an instance
--   - generalization: the run's total query count Q (terminates at a query exactly when its fresh index is the current source index j) → for every probability space Ω of other randomness and every target rule g(η, ℓ₁, …, ℓ_{i−1}) measurable in η, the product measure of the event that no query ℓ_i (i < r) equals its target is (1 − 1/M)^r; reason: the current source index is such a function of the proposals and the earlier queries, and Q > r is exactly that event; the statement covers every such rule
--   - encoding: choose j with probability q^{|I_j|}/W₀ and include each vertex with probability λ/q → these finite choices are written as their explicit probabilities; the query stream is a random element of ℕ → Fin M under the product of uniform laws; reason: the same probabilities; only the infinite query stream needs a measure
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with λ > 0; reason: the statement is about the combinatorial weights and probabilities only and holds for every real λ > 0; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9, Sampling from the union and Work and truncation, p.11

import Mathlib
import Definitions.Def_ThreshRankBIS_unionTrial
set_option autoImplicit false
open Finset MeasureTheory

namespace ThreshRankBIS

/-- **Proof of Lemma 9: sampling from the union**, p.11. Let `I_1, …, I_M` (`M ≥ 1`) be a list of
finite sets, `λ > 0`, `q = 1 + λ`, `W_0 = ∑_j q^{|I_j|}`, `a(J) = |{j : J ⊆ I_j}|` and
`Z = ∑_{J ∈ ⋃_j 2^{I_j}} λ^{|J|}`. For one trial (choose `j` with probability `q^{|I_j|}/W_0`,
include each element of `I_j` with probability `λ/q`, query fresh uniform `ℓ ∈ [M]` until
`J ⊆ I_ℓ`, accept iff `ℓ = j`):
1. the proposal probability of `J` is `a(J)λ^{|J|}/W_0`;
2. for `J ⊆ I_j`, the first containing index equals `j` with probability `1/a(J)`;
3. a trial accepts `J` with probability `λ^{|J|}/W_0`, for every `J` in the union;
4. a trial accepts with total probability `Z/W_0`;
5. conditional on acceptance the output is `J` with probability `λ^{|J|}/Z` (the required
   distribution);
6. the total query count `Q` satisfies `Pr(Q > r) = (1 − 1/M)^r ≤ e^{−r/M}` for `r ≥ 1`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9,
*Sampling from the union* and *Work and truncation*, p.11.

**Formalization Note.** Clause 6 is stated for the structure the paper's argument uses: the
queries `ℓ_1, ℓ_2, …` are fresh i.i.d. uniform indices, independent of all other randomness `η`
(the proposals of the successive trials), and the run terminates at query `i` exactly when `ℓ_i`
equals the current source index, which is a function `g(η, ℓ_1, …, ℓ_{i−1})` of the history. For
every such `g`, `Q > r` is the event that none of the first `r` queries hits its target. -/
theorem lemma_9_trial {α : Type} [DecidableEq α] {M : ℕ} [NeZero M] (I : Fin M → Finset α)
    (lam : ℝ) (hlam : 0 < lam) :
    (∀ J : Finset α, proposalProb I lam J = (mult I J : ℝ) * lam ^ #J / W0 I lam) ∧
    (∀ (J : Finset α) (j : Fin M), J ⊆ I j →
      (queryMeasure M).real {ω | firstContaining I J ω = some j} = 1 / (mult I J : ℝ)) ∧
    (∀ J ∈ unionFamily I, acceptProb I lam J = lam ^ #J / W0 I lam) ∧
    (∑ J ∈ unionFamily I, acceptProb I lam J = unionWeight I lam / W0 I lam) ∧
    (∀ J ∈ unionFamily I,
      acceptProb I lam J / (unionWeight I lam / W0 I lam) = lam ^ #J / unionWeight I lam) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (g : Ω → List (Fin M) → Fin M), (∀ l, Measurable (fun η => g η l)) →
      ∀ r : ℕ, 1 ≤ r →
        (ν.prod (queryMeasure M)).real
            {p | ∀ i < r, p.2 i ≠ g p.1 (List.ofFn (fun i' : Fin i => p.2 i'))} =
          (1 - 1 / (M : ℝ)) ^ r ∧
        (1 - 1 / (M : ℝ)) ^ r ≤ Real.exp (-(r : ℝ) / M)) := by sorry

end ThreshRankBIS
