-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_Supplement_theorem_5_4
-- name    : SortingCounterexamples.Optimal.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:28.180519+00:00
-- url     : https://prove2.me/theorems/ae392c70-26a9-4063-856d-be765cb43e44
-- title:
--   Theorem 5.4 — for every $2\le d\le n$ some $d$-dimensional geometric class forces $\Omega(d\log n+dk)$ expected queries
-- statement:
--   There is an absolute constant $c>0$ such that for all integers $2\le d\le n$ there are vectors $v_1,\dots,v_n\in\mathbb R^d$ and a finite class $H$ of rankings of the $n$ items, each induced by some direction $w\in\mathbb R^d$, with the following property, where $H$ is chosen before $k$ and before the learner. For every $k\ge0$ and every randomized learner $(L_\omega)_{\omega\in\Omega}$ whose queries are linear orders (seed $\omega$ from an arbitrary probability space $(\Omega,\mu)$, each decision measurable in $\omega$; the learner may know $k$ and $H$, and its queries need not lie in $H$) there are a target $\sigma\in H$, fixed independently of the seed, and an oracle returning at most $k$ untruthful counterexamples for $\sigma$ against every sequence of queries, such that
--   $$\mathbb E_{\omega\sim\mu}\bigl[Q(L_\omega)\bigr]\ \ge\ c\,(d\log n+dk),$$
--   where $Q\in\{1,2,\dots\}\cup\{\infty\}$ is the number of queries until approval.
--
--   This is the lower half of Theorem 1.2: the dependence on $k$ of Theorem 5.1 is tight, and a factor $d$ remains open in the noiseless term.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so a learner that fails to terminate with positive probability has infinite cost; it is not excluded by an assumption.
--
--   Differences from the source:
--   - encoding: Ω(d log n + dk) worst-case expected query complexity → ∃ c > 0 before n, d, the class, k and the learner; ∃ σ ∈ H and an oracle with ofReal (c · (d log n + d k)) ≤ ∫⁻ Q dμ; reason: this is the meaning of an Ω bound on the worst case over targets in the class and oracles, uniform in all parameters; natural logarithm
--   - encoding: possibly randomized learner whose queries are linear orders → a family of deterministic learners indexed by a seed of a probability space (Ω : Type), decisions measurable in the seed; reason: drawing all private randomness at the start covers every randomized learner; measurability is needed for the expectation to exist
--   - encoding: in the presence of at most k untruthful counterexamples → a deterministic transcript-dependent oracle with at most k lies against every query sequence; reason: the source's hard oracles are of this kind; requiring validity against every query sequence only strengthens the existence claim
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 27 / PDF p. 28, Theorem 5.4 (proof to printed p. 29 / PDF p. 30); lower half of Theorem 1.2, printed p. 4 / PDF p. 5; model and randomized cost measure printed p. 1 / PDF p. 2

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

open MeasureTheory
open scoped ENNReal

namespace SortingCounterexamples.Optimal.Supplement

open SortingCounterexamples.Optimal

/-- Theorem 5.4: there is an absolute `c > 0` such that for every `2 ≤ d ≤ n` there is a
`d`-dimensional geometric class `H` of rankings of `n` items (with a representation `v`),
chosen before `k` and the learner, such that for every `k` and every randomized learner whose
queries are linear orders there are a fixed target `σ ∈ H` and an oracle with at most `k`
untruthful counterexamples against every query sequence forcing expected number of queries at
least `c (d log n + d k)`. -/
theorem theorem_5_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ), 2 ≤ d → d ≤ n →
      ∃ (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n)), IsGeometricClass v H ∧
        ∀ k : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (L : Ω → DetLearner n), IsRandomizedLearner L →
          ∃ σ ∈ H, ∃ O : Oracle n, Admissible O σ k ∧
            ENNReal.ofReal (c * lowerRate n d k) ≤
              ∫⁻ ω, ((queries (L ω) O : ℕ∞) : ℝ≥0∞) ∂μ := by sorry

end SortingCounterexamples.Optimal.Supplement
