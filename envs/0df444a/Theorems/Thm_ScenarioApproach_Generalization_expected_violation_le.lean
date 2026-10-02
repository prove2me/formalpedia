-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_expected_violation_le
-- name    : ScenarioApproach.Generalization.expected_violation_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:46:43.48645+00:00
-- url     : https://prove2.me/theorems/f4f7ddfc-0e38-48fa-ba78-041ebc41ed98
-- title:
--   Theorem 3.8 — the expected violation is at most $d/(N+1)$
-- statement:
--   Consider the convex scenario program with $d\ge1$ decision variables, cost $c^T\theta$, domain $\Theta$, constraint sets $\Theta_\delta$, $\delta\in\Delta$, and probability $\mathbb P$ on $\Delta$, under Assumption 3.4 ($\Theta$ and all $\Theta_\delta$ convex and closed) and Assumption 3.6 (a unique solution for every number of constraints and every sample). Let $\theta^*$ be the solution of the program with $N$ i.i.d. constraints $\delta_1,\dots,\delta_N\sim\mathbb P$. Then its violation $V(\theta^*)$ is integrable and
--
--   $$
--   \mathbb E[V(\theta^*)]\le\frac{d}{N+1}.
--   $$
--
--   Equivalently, $d/(N+1)$ bounds the probability that the scenario solution computed from $N$ samples violates the constraint of a further, independent sample; it is the mean of the Beta$(d,N-d+1)$ distribution that dominates $V(\theta^*)$ by Theorem 3.7.
--
--   **Formalization Note** The expectation is the Bochner integral of $\omega\mapsto V(\theta^*(\omega))$ under $\mathbb P^N$ = `Measure.pi (fun _ : Fin N => P)`; integrability is part of the conclusion, so the bound cannot hold through Lean's convention that a non-integrable function integrates to $0$. No relation between $N$ and $d$ is assumed, as on the page (the bound exceeds $1$ when $N<d$). Measurability is assumed as for Theorem 3.7.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 42, Theorem 3.8, Eq. (3.11)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

namespace ScenarioApproach.Generalization

/-- Theorem 3.8 (p. 42): under Assumptions 3.4 and 3.6, `𝔼[V(θ*)] ≤ d / (N + 1)`. The
violation of the scenario solution is integrable and its expectation under `ℙ^N` is at most
`d / (N + 1)`. -/
theorem expected_violation_le
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
    (hd : 1 ≤ d) :
    MeasureTheory.Integrable (fun ω => violation P Θδ (θstar ω))
        (MeasureTheory.Measure.pi fun _ : Fin N => P) ∧
      ∫ ω, violation P Θδ (θstar ω) ∂(MeasureTheory.Measure.pi fun _ : Fin N => P) ≤
        (d : ℝ) / (N + 1) := by sorry

end ScenarioApproach.Generalization
