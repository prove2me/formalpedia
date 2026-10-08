-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_violation_tail_le_removal_bound_two_dim
-- name    : ScenarioApproach.Removal.violation_tail_le_removal_bound_two_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:38.597977+00:00
-- url     : https://prove2.me/theorems/64399033-7170-4c68-98a8-24814f629a0b
-- title:
--   Theorem 3.9 for $d = 2$ — $\mathbb P^N\{V(\theta^*_k) > \varepsilon\} \le \binom{k+1}{k}\sum_{i=0}^{k+1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}$
-- statement:
--   Consider the convex scenario program in dimension $d = 2$ with $N \ge 2$ independent constraints, under Assumptions 3.4 and 3.6. Let an arbitrary removal procedure select, as a function of the sample, $k \le N$ constraints to remove, and let $\theta^*_k$ be the solution of the program without them, where the procedure ensures that $\theta^*_k$ violates exactly the $k$ removed constraints. Then for every $\varepsilon \in [0,1]$
--
--   $$
--   \mathbb P^N\{(\delta_1,\dots,\delta_N) \in \Delta^N : V(\theta^*_k) > \varepsilon\} \le \binom{k+1}{k} \sum_{i=0}^{k+1} \binom Ni \varepsilon^i (1-\varepsilon)^{N-i},
--   $$
--
--   which is (3.13) for $d = 2$.
--
--   This is the case of Theorem 3.9 that the book proves in full, by combining the covering (5.11) with the per-index-set bound (5.14).
--
--   **Formalization Note** The removal procedure is a map from samples to $k$-element index sets, arbitrary otherwise; $\theta^*_k$ solves the program without the selected constraints for every sample and violates each of them with probability one (as in the book's proof, p. 65; "for every sample" would be unsatisfiable for $1 \le k < N$, since a sample with repeated values forces a kept constraint to equal a removed one). Measurability, implicit in the book, is explicit: the constraint relation is jointly measurable, the solution map of the scenario program with $m$ constraints is measurable for every $m$, and $\theta^*_k$ is measurable.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 66, closing display of Section 5.3 (Theorem 3.9, Eq. (3.13), for d = 2)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_tail_le_removal_bound_two_dim {N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin 2))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2))
    (hconv : ConvexClosedConstraints Θ Θδ)
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × Δ | p.1 ∈ Θδ p.2})
    (hsol_meas : ∀ (m : ℕ) (θs : (Fin m → Δ) → EuclideanSpace ℝ (Fin 2)),
      (∀ ω, IsSolution Θ Θδ c ω (θs ω)) → Measurable θs)
    (hN : 2 ≤ N) (hkN : k ≤ N)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin 2))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (hθk_meas : Measurable θk)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P) {ω | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} ≤
      ENNReal.ofReal (((k + 1).choose k : ℝ) *
        ∑ i ∈ Finset.range (k + 2), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Removal
