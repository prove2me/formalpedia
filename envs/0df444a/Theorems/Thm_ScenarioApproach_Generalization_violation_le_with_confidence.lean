-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_violation_le_with_confidence
-- name    : ScenarioApproach.Generalization.violation_le_with_confidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:49:02.32251+00:00
-- url     : https://prove2.me/theorems/0fe6f31b-06ac-498e-be9c-97d57ac9305b
-- title:
--   Theorem 1.3 — $N\ge\frac{2}{\varepsilon}(\ln\frac1\beta+d-1)$ scenarios give violation $\le\varepsilon$ with confidence $1-\beta$
-- statement:
--   Consider the convex scenario program with $d\ge1$ decision variables, cost $c^T\theta$, domain $\Theta$, constraint sets $\Theta_\delta$, $\delta\in\Delta$, and probability $\mathbb P$ on $\Delta$, under Assumption 3.4 ($\Theta$ and all $\Theta_\delta$ convex and closed) and Assumption 3.6 (a unique solution for every number of constraints and every sample). Let $\varepsilon\in(0,1)$ (violation parameter) and $\beta\in(0,1)$ (confidence parameter). If the number of scenarios $N$ satisfies
--
--   $$
--   N\ge\frac{2}{\varepsilon}\Big(\ln\frac1\beta+d-1\Big),
--   $$
--
--   then, with probability at least $1-\beta$ over the i.i.d. sample $\delta_1,\dots,\delta_N\sim\mathbb P$, the solution $\theta^*$ satisfies
--
--   $$
--   \mathbb P\{\delta\in\Delta:\ \theta^*\notin\Theta_\delta\}\le\varepsilon .
--   $$
--
--   This is the explicit sample-size form of the generalization theorem: the number of scenarios needed grows like $1/\varepsilon$ and only logarithmically in $1/\beta$.
--
--   **Formalization Note** The book states Theorem 1.3 informally ("full rigor is sacrificed", p. 12) and obtains it in §3.2.1 as a corollary of Theorem 3.7; the assumptions of Theorem 3.7 (Assumptions 3.4, 3.6) are therefore hypotheses here, together with the measurability conventions of this mission. The event is $\{\omega: V(\theta^*(\omega))\le\varepsilon\}$ under `Measure.pi (fun _ : Fin N => P)`, compared with `ENNReal.ofReal (1 - β)`.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 20, Theorem 1.3; pp. 41–42, §3.2.1

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

namespace ScenarioApproach.Generalization

/-- Theorem 1.3 (p. 20), obtained in §3.2.1 (pp. 41–42) as a corollary of Theorem 3.7: for
`ε, β ∈ (0, 1)` and `N ≥ (2/ε)(ln(1/β) + d - 1)`, with probability at least `1 - β` the
scenario solution satisfies `ℙ{δ ∈ Δ : θ* ∉ Θ_δ} ≤ ε`. -/
theorem violation_le_with_confidence
    {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    -- Assumption 3.4 (convexity): `Θ` and every `Θ_δ` are convex and closed
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    -- Assumption 3.6 (existence and uniqueness), for every `m` and every sample
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    -- measurability, glossed over on p. 33: the constraint relation is jointly measurable
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    -- `θstar ω` is the solution of the scenario program with the `N` sampled constraints `ω`
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hd : 1 ≤ d) (ε β : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN : 2 / ε * (Real.log (1 / β) + (d : ℝ) - 1) ≤ (N : ℝ)) :
    ENNReal.ofReal (1 - β) ≤
      MeasureTheory.Measure.pi (fun _ : Fin N => P) {ω | violation P Θδ (θstar ω) ≤ ε} := by sorry

end ScenarioApproach.Generalization
