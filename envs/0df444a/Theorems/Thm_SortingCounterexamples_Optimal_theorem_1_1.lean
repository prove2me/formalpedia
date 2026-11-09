-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_theorem_1_1
-- name    : SortingCounterexamples.Optimal.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:46.767958+00:00
-- url     : https://prove2.me/theorems/c10ed885-857e-4ebb-b562-18ea5136307c
-- title:
--   Theorem 1.1 — the optimal number of queries is $\Theta(n\log n+nk)$, attained by a deterministic learner that does not know $k$
-- statement:
--   Let $f(n,k)=n\log n+nk$. There are absolute constants $C,c>0$ such that:
--
--   1. **Upper bound.** There is a family of deterministic proper learners $(A_n)_{n}$, one for each number of items and not depending on $k$, such that for every $n\ge2$, every $k\ge0$, every target ranking $\sigma$ and every adaptive oracle whose responses to $A_n$ contain at most $k$ untruthful counterexamples, $A_n$ obtains approval after
--   $$Q(A_n)\ \le\ C\,f(n,k)$$
--   queries, the approved query included.
--   2. **Lower bound.** For every $n\ge2$, every $k\ge0$ and every randomized proper learner (seed from an arbitrary probability space, decisions measurable in the seed, knowledge of $k$ allowed), there are a fixed target ranking and an oracle with at most $k$ untruthful counterexamples against every query sequence such that the expected number of queries is at least $c\,f(n,k)$.
--
--   Approval is decided only by the oracle; it need not certify that the approved ranking is the target.
--
--   **Formalization Note** The query count lives in $\{1,2,\dots\}\cup\{\infty\}$ with $\infty$ for non-termination, and expectations are taken in $[0,\infty]$, so neither bound can hold by a default value.
--
--   Differences from the source:
--   - reading: Θ(n log n + nk) for n items, no explicit domain → n ≥ 2 and every k ≥ 0; reason: the domain of Theorem 4.5; at n = 1, k = 0 the rate is 0 while one query is always made
--   - encoding: the optimal number of queries is Θ(n log n + nk) → ∃ C > 0 and a k-independent learner family with Q ≤ ofReal (C · f(n,k)); ∃ c > 0 with the randomized lower bound; reason: Θ means both constants exist; they are placed before n, k, targets, oracles and learners; natural logarithm
--   - encoding: at most k untruthful counterexamples (upper bound) → every transcript of the run of A_n against the oracle has at most k lies for σ; reason: this is exactly every adaptive response path with at most k lies against the deterministic learner
--   - encoding: possibly randomized proper learner → a family of deterministic learners indexed by a seed of a probability space (Ω : Type), decisions measurable in the seed; reason: drawing all private randomness at the start covers every randomized learner; measurability is needed for the expectation to exist
--   - encoding: an oracle using at most k untruthful counterexamples → a deterministic transcript-dependent oracle with at most k lies against every query sequence; reason: the source's hard oracles are of this kind; requiring validity against every query sequence only strengthens the existence claim
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 3 / PDF p. 4, Theorem 1.1; model on printed p. 1 / PDF p. 2; domain n ≥ 2, k ≥ 0 from Theorem 4.5, printed p. 19 / PDF p. 20; upper-bound completion printed p. 19 / PDF p. 20

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol

open MeasureTheory
open scoped ENNReal

namespace SortingCounterexamples.Optimal

/-- Theorem 1.1: the optimal number of queries is `Θ(n log n + n k)`.
(1) Upper bound: one deterministic learner per `n`, chosen before and independently of `k`,
obtains approval within `C (n log n + n k)` queries against every oracle whose responses
include at most `k` untruthful counterexamples, for every target.
(2) Lower bound: every randomized proper learner has, for some fixed target and valid oracle
with at most `k` lies, expected number of queries at least `c (n log n + n k)`. -/
theorem theorem_1_1 :
    (∃ C : ℝ, 0 < C ∧ ∃ A : (n : ℕ) → DetLearner n, ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      ∀ (σ : Ranking n) (O : Oracle n), RunAdmissible (A n) O σ k →
        ((queries (A n) O : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * rate n k)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (L : Ω → DetLearner n), IsRandomizedLearner L →
        ∃ (σ : Ranking n) (O : Oracle n), Admissible O σ k ∧
          ENNReal.ofReal (c * rate n k) ≤ ∫⁻ ω, ((queries (L ω) O : ℕ∞) : ℝ≥0∞) ∂μ) := by sorry

end SortingCounterexamples.Optimal
