-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_theorem_4_5
-- name    : SortingCounterexamples.Optimal.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:49.536323+00:00
-- url     : https://prove2.me/theorems/4608dc16-57ee-4657-97ca-08df772e4121
-- title:
--   Theorem 4.5 — every randomized proper learner needs $\Omega(n\log n+nk)$ expected queries
-- statement:
--   There is an absolute constant $c>0$ such that for every $n\ge2$, every $k\ge0$ and every randomized proper learner $(L_\omega)_{\omega\in\Omega}$ (seed $\omega$ drawn from an arbitrary probability space $(\Omega,\mu)$, each decision measurable in $\omega$; the learner may depend on $n$ and $k$), there are a target ranking $\sigma$, fixed independently of the seed, and an oracle that returns at most $k$ untruthful counterexamples for $\sigma$ against every sequence of queries, such that
--   $$\mathbb E_{\omega\sim\mu}\bigl[Q(L_\omega)\bigr]\ \ge\ c\,(n\log n+nk),$$
--   where $Q\in\{1,2,\dots\}\cup\{\infty\}$ is the number of queries until approval.
--
--   The two terms come from different hard instances; the bound is the maximum of the two, up to a factor $2$.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so a learner that fails to terminate with positive probability has infinite cost and satisfies the bound; it is not excluded by an assumption.
--
--   Differences from the source:
--   - encoding: Ω(n log n + nk) worst-case expected query complexity → ∃ c > 0 before n, k and the learner; ∃ target and oracle with ofReal (c · (n log n + n k)) ≤ ∫⁻ Q dμ; reason: this is the meaning of an Ω bound on the worst case over targets and oracles; natural logarithm
--   - encoding: possibly randomized proper learner → a family of deterministic learners indexed by a seed of a probability space (Ω : Type), decisions measurable in the seed; reason: drawing all private randomness at the start covers every randomized learner; measurability is needed for the expectation to exist
--   - encoding: an oracle using at most k untruthful counterexamples → a deterministic transcript-dependent oracle with at most k lies against every query sequence; reason: the source's hard oracles are of this kind; requiring validity against every query sequence only strengthens the existence claim
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 19 / PDF p. 20, Theorem 4.5 (proof to printed p. 21 / PDF p. 22); model and randomized cost measure from printed p. 1 / PDF p. 2

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol

open MeasureTheory
open scoped ENNReal

namespace SortingCounterexamples.Optimal

/-- Theorem 4.5: there is an absolute `c > 0` such that for every `n ≥ 2` and `k ≥ 0`, every
randomized proper learner has, for some fixed target `σ` and some valid oracle with at most
`k` lies, expected number of queries at least `c (n log n + n k)`. -/
theorem theorem_4_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (L : Ω → DetLearner n), IsRandomizedLearner L →
        ∃ (σ : Ranking n) (O : Oracle n), Admissible O σ k ∧
          ENNReal.ofReal (c * rate n k) ≤ ∫⁻ ω, ((queries (L ω) O : ℕ∞) : ℝ≥0∞) ∂μ := by sorry

end SortingCounterexamples.Optimal
