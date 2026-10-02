-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_violation_tail_two_scenarios_of_fullySupported
-- name    : ScenarioApproach.Generalization.violation_tail_two_scenarios_of_fullySupported
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:43:27.998035+00:00
-- url     : https://prove2.me/theorems/6b909167-ef4c-4d9f-8a30-7c955a6659e0
-- title:
--   Eq. (5.3) — two scenarios in the plane: $\mathbb P^2\{V(\theta^*)>\varepsilon\}=1-\varepsilon^2$
-- statement:
--   Consider a convex scenario program in $\mathbb R^2$ ($d=2$) with cost $c^T\theta$, domain $\Theta$, constraint sets $\Theta_\delta$, $\delta\in\Delta$, and probability $\mathbb P$ on $\Delta$, satisfying Assumption 3.4 (convex closed sets) and Assumption 3.6 (a unique solution for every number $m$ of constraints and every sample), and fully supported (Definition 5.4). Let $\theta^*$ be the solution of the program with $N=2$ i.i.d. constraints $\delta_1,\delta_2\sim\mathbb P$. Then for every $\varepsilon\in[0,1]$
--
--   $$
--   \mathbb P^2\{V(\theta^*)>\varepsilon\}=\sum_{i=0}^{1}\binom{2}{i}\varepsilon^i(1-\varepsilon)^{2-i}=1-\varepsilon^2 .
--   $$
--
--   This is the equality (5.2) for $N=2$, the base case from which the book derives the general-$N$ equality for fully supported problems in the plane.
--
--   **Formalization Note** Same conventions as the general equality: `θstar : (Fin 2 → Δ) → EuclideanSpace ℝ (Fin 2)` is the solution map, measurability is assumed as joint measurability of the constraint relation and of `θstar`, and the conclusion is `ENNReal.ofReal (1 - ε ^ 2)`.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 58, Eq. (5.3)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint

namespace ScenarioApproach.Generalization

/-- Eq. (5.3) (p. 58): for a fully supported problem with `d = 2` decision variables and
`N = 2` scenarios, `ℙ²{V(θ*) > ε} = 1 - ε²`. -/
theorem violation_tail_two_scenarios_of_fullySupported
    {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin 2)) (Θ : Set (EuclideanSpace ℝ (Fin 2)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin 2)))
    -- Assumption 3.4 (convexity): `Θ` and every `Θ_δ` are convex and closed
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    -- Assumption 3.6 (existence and uniqueness), for every `m` and every sample
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    -- measurability, glossed over on p. 33: the constraint relation is jointly measurable
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × Δ | p.1 ∈ Θδ p.2})
    -- `θstar ω` is the solution of the scenario program with the `N` sampled constraints `ω`
    (θstar : (Fin 2 → Δ) → EuclideanSpace ℝ (Fin 2))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hfs : FullySupported c Θ Θδ P) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin 2 => P) {ω | ε < violation P Θδ (θstar ω)} =
      ENNReal.ofReal (1 - ε ^ 2) := by sorry

end ScenarioApproach.Generalization
