-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_3
-- name    : SeqSocialLearning.Adequate.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:11.665759+00:00
-- url     : https://prove2.me/theorems/924187c5-0fb8-4f4b-988e-d753e3ba081e
-- title:
--   Lemma 3, p. 12 — u ∈ U is jointly uniformly continuous on a compact set of measure ≥ 1 − ε
-- statement:
--   Let $\Omega$ be a separable complete metric space with a probability measure $\mu$, let $A$ be a compact metric space, and let $u \in U$: bounded, jointly measurable, and continuous in the action for every fixed state.
--
--   For every $\varepsilon > 0$ and $\gamma > 0$ there exist a compact set $E \subseteq \Omega$ with $\mu(E) \ge 1 - \varepsilon$ and constants $\eta, \beta > 0$ such that for all $\omega, \omega' \in E$ and $a, a' \in A$,
--   $$
--   d_\Omega(\omega,\omega') \le \beta \ \text{ and } \ d_A(a,a') \le \eta \implies |u(a,\omega) - u(a',\omega')| \le \gamma .
--   $$
--
--   Lemma 3 is the regularity tool behind Lemma 4 and the proof of Lemma 8.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 12, Lemma 3

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 3** (p. 12). For a utility `u ∈ U` and every `ε, γ > 0` there are a compact set
`E ⊆ Ω` with `µ(E) ≥ 1 − ε` and constants `η, β > 0` such that `u` varies by at most `γ`
between `(a, ω)` and `(a', ω')` whenever `ω, ω' ∈ E`, `d_Ω(ω, ω') ≤ β` and `d_A(a, a') ≤ η`. -/
theorem lemma_3 {Ω A : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : A → Ω → ℝ) (hu : InU u) (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ E : Set Ω, IsCompact E ∧ 1 - ε ≤ μ.real E ∧
      ∃ η β : ℝ, 0 < η ∧ 0 < β ∧
        ∀ ω ∈ E, ∀ ω' ∈ E, ∀ a a' : A, dist ω ω' ≤ β → dist a a' ≤ η →
          |u a ω - u a' ω'| ≤ γ := by sorry

end SeqSocialLearning.Adequate
