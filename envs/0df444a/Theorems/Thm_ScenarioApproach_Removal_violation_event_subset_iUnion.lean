-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_violation_event_subset_iUnion
-- name    : ScenarioApproach.Removal.violation_event_subset_iUnion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:17.897074+00:00
-- url     : https://prove2.me/theorems/3831e510-fab4-47fa-8cf2-cf26bb0f5d44
-- title:
--   Eq. (5.11) — the event $V(\theta^*_k) > \varepsilon$ is covered by the events $\Delta^N_I \cap \{V(\theta^*_I) > \varepsilon\}$
-- statement:
--   Let $(\delta_1,\dots,\delta_N)$ be a sample and let a removal procedure select, as a function of the sample, a set $I(\delta_1,\dots,\delta_N)$ of exactly $k$ indexes. Let $\theta^*_k$ be the solution of the scenario program without the constraints with index in this set, and suppose that, with probability one, $\theta^*_k$ violates each of these $k$ removed constraints. For every set $I$ of $k$ indexes let $\theta^*_I$ be the solution of the program without the constraints in $I$, and let
--
--   $$
--   \Delta^N_I = \{(\delta_1,\dots,\delta_N) \in \Delta^N : \theta^*_I \text{ violates the constraints } \theta \in \Theta_{\delta_{i}},\ i \in I\}.
--   $$
--
--   Under Assumption 3.6, for every $\varepsilon$,
--
--   $$
--   \{(\delta_1,\dots,\delta_N) \in \Delta^N : V(\theta^*_k) > \varepsilon\} \subseteq \bigcup_{I \in \mathcal I} \{(\delta_1,\dots,\delta_N) \in \Delta^N_I : V(\theta^*_I) > \varepsilon\}
--   $$
--
--   up to a zero probability set, where $\mathcal I$ is the collection of all choices of $k$ indexes from $\{1,\dots,N\}$.
--
--   This inclusion reduces the analysis of an arbitrary removal procedure to the analysis of finitely many fixed index sets, which is the first step of the proof of Theorem 3.9.
--
--   **Formalization Note** As on the page, the removed constraints are assumed violated with probability one (`∀ᵐ` under $\mathbb P^N$), and the inclusion holds up to a zero probability set: for $\mathbb P^N$-almost every sample, membership in the left-hand event implies membership in the union. (Requiring the violation for every sample would be unsatisfiable for $1 \le k < N$: on a sample with all $\delta_i$ equal, a kept constraint coincides with a removed one.) The removal rule and the solution maps $\theta^*_k$, $\theta^*_I$ are arbitrary functions of the sample satisfying the stated solution properties; Assumption 3.6 (applied to the $N-k$ kept constraints) makes $\theta^*_I$ unique.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 65, Eq. (5.11); p. 64, Eqs. (5.9)–(5.10)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_event_subset_iUnion {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (θI : Finset (Fin N) → (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθI : ∀ J ω, IsSolutionWithout Θ Θδ c ω J (θI J ω))
    (ε : ℝ) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)),
      ω ∈ {ω : Fin N → Δ | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} →
        ω ∈ ⋃ J ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
          {ω : Fin N → Δ | (∀ i ∈ J, θI J ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θI J ω)} := by sorry

end ScenarioApproach.Removal
