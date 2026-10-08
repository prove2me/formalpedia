-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_removed_event_prob_le_two_dim
-- name    : ScenarioApproach.Removal.removed_event_prob_le_two_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:23.508736+00:00
-- url     : https://prove2.me/theorems/803e14ab-2c17-4d40-85fd-5d34ce74fcad
-- title:
--   Eq. (5.14) — bound for one index set $I$ in dimension $d = 2$
-- statement:
--   Consider the convex scenario program in dimension $d = 2$, under Assumptions 3.4 and 3.6. Fix a set $I$ of $k$ indexes from $\{1,\dots,N\}$ with $N \ge k+2$, let $\theta^*_I$ be the solution of the program without the constraints with index in $I$, and let $\Delta^N_I$ be the set of samples for which $\theta^*_I$ violates all $k$ removed constraints. Then for every $\varepsilon \in [0,1]$
--
--   $$
--   \mathbb P^N\{(\delta_1,\dots,\delta_N) \in \Delta^N_I : V(\theta^*_I) > \varepsilon\} \le \frac{2\binom{N-k}{2}}{(k+2)\binom{N}{k+2}} \sum_{i=0}^{k+1} \binom Ni \varepsilon^i (1-\varepsilon)^{N-i}.
--   $$
--
--   Summed over the $\binom Nk$ choices of $I$, this bound yields Theorem 3.9 in dimension two.
--
--   **Formalization Note** The book writes this display for $d = 2$ only; it is stated here for `EuclideanSpace ℝ (Fin 2)`. The hypothesis $N \ge k+2$ is implicit on the page (the Beta density $2\binom{N-k}{2}\alpha(1-\alpha)^{N-k-2}$ and $\binom{N}{k+2}$ in the denominator require it). Measurability is explicit: jointly measurable constraint relation and measurable $\theta^*_I$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 66, Eq. (5.14)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem removed_event_prob_le_two_dim {N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin 2))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2))
    (hconv : ConvexClosedConstraints Θ Θδ)
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × Δ | p.1 ∈ Θδ p.2})
    (hkN : k + 2 ≤ N)
    (J : Finset (Fin N)) (hJ : J.card = k)
    (θJ : (Fin N → Δ) → EuclideanSpace ℝ (Fin 2))
    (hθJ : ∀ ω, IsSolutionWithout Θ Θδ c ω J (θJ ω))
    (hθJ_meas : Measurable θJ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P)
        {ω | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θJ ω)} ≤
      ENNReal.ofReal (2 * ((N - k).choose 2 : ℝ) / (((k : ℝ) + 2) * (N.choose (k + 2) : ℝ)) *
        ∑ i ∈ Finset.range (k + 2), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Removal
