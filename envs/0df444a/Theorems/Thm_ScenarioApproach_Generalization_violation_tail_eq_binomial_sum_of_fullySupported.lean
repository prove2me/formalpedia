-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_violation_tail_eq_binomial_sum_of_fullySupported
-- name    : ScenarioApproach.Generalization.violation_tail_eq_binomial_sum_of_fullySupported
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:38:35.914535+00:00
-- url     : https://prove2.me/theorems/cffaa932-832c-42ca-9e81-1848ffab7e34
-- title:
--   Eq. (5.2) — for fully supported problems Theorem 3.7 holds with equality
-- statement:
--   Consider the convex scenario program with $d$ decision variables: cost $c^T\theta$, domain $\Theta\subseteq\mathbb R^d$, constraint sets $\Theta_\delta$, $\delta\in\Delta$, and a probability $\mathbb P$ on $\Delta$. Assume
--
--   1. (Assumption 3.4) $\Theta$ and every $\Theta_\delta$ are convex and closed;
--   2. (Assumption 3.6) for every $m$ and every sample $(\delta_1,\dots,\delta_m)$ the program with these $m$ constraints has a unique solution;
--   3. the problem is fully supported (Definition 5.4): for every $m\ge d$, with probability 1 the program with $m$ i.i.d. constraints has exactly $d$ support constraints.
--
--   Let $1\le d\le N$, let $\theta^*$ be the solution of the program with $N$ i.i.d. constraints $\delta_1,\dots,\delta_N\sim\mathbb P$, and $V(\theta^*)$ its violation. Then for every $\varepsilon\in[0,1]$
--
--   $$
--   \mathbb P^N\{V(\theta^*)>\varepsilon\}=\sum_{i=0}^{d-1}\binom{N}{i}\varepsilon^i(1-\varepsilon)^{N-i}.
--   $$
--
--   So the bound of Theorem 3.7 is attained exactly by fully supported problems: $V(\theta^*)$ then has the Beta$(d,N-d+1)$ distribution, whatever $\mathbb P$ is.
--
--   **Formalization Note** The book writes the display (5.2) for $d=2$ and states in words that the result of Theorem 3.7 holds with equality for fully supported problems; the general-$d$ equality is stated here. The solution is a map `θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d)` with `θstar ω` the solution for every sample. Measurability, glossed over in the book (p. 33), is assumed as joint measurability of $\{(\theta,\delta):\theta\in\Theta_\delta\}$ and measurability of `θstar`. The probability is compared in $[0,\infty]$ via `ENNReal.ofReal`.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 58, text after Definition 5.4 and Eq. (5.2)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint

namespace ScenarioApproach.Generalization

/-- Eq. (5.2) and the sentence before §5.2 (p. 58): for fully supported problems the bound of
Theorem 3.7 holds with equality. -/
theorem violation_tail_eq_binomial_sum_of_fullySupported
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
    (hfs : FullySupported c Θ Θδ P)
    (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P) {ω | ε < violation P Θδ (θstar ω)} =
      ENNReal.ofReal
        (∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Generalization
