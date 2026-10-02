-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_violation_tail_le_binomial_sum
-- name    : ScenarioApproach.Generalization.violation_tail_le_binomial_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:50:40.48288+00:00
-- url     : https://prove2.me/theorems/3f312ca3-ed03-427c-bb92-deaadae1a406
-- title:
--   Theorem 3.7 — $\mathbb P^N\{V(\theta^*)>\varepsilon\}\le\sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}$
-- statement:
--   Consider the convex scenario program with $d$ decision variables:
--
--   $$
--   \min_{\theta\in\Theta}c^T\theta\quad\text{subject to}\quad\theta\in\bigcap_{i=1}^{N}\Theta_{\delta_i},
--   $$
--
--   where $c\in\mathbb R^d$, $\Theta\subseteq\mathbb R^d$, $\{\Theta_\delta,\ \delta\in\Delta\}$ is a family of constraint sets indexed by an uncertain parameter, and $\delta_1,\dots,\delta_N$ are independent samples from a probability $\mathbb P$ on $\Delta$. Assume
--
--   1. (Assumption 3.4) $\Theta$ and every $\Theta_\delta$ are convex and closed;
--   2. (Assumption 3.6) for every $m=0,1,2,\dots$ and every sample $(\delta_1,\dots,\delta_m)$ the program with these $m$ constraints has a solution, and it is unique.
--
--   Let $1\le d\le N$, let $\theta^*$ be the solution of the program with the $N$ sampled constraints, and let $V(\theta^*)=\mathbb P\{\delta:\theta^*\notin\Theta_\delta\}$ be its violation (Definition 3.1). Then for every $\varepsilon\in[0,1]$
--
--   $$
--   \mathbb P^N\{V(\theta^*)>\varepsilon\}\le\sum_{i=0}^{d-1}\binom{N}{i}\varepsilon^i(1-\varepsilon)^{N-i}.
--   $$
--
--   The right-hand side is the tail of a Beta$(d,N-d+1)$ distribution; it depends on the problem only through $d$ and holds whatever $\mathbb P$ is. This is the generalization theorem of the scenario approach.
--
--   **Formalization Note** The decision space is `EuclideanSpace ℝ (Fin d)` and a sample is `ω : Fin N → Δ` with law `Measure.pi (fun _ : Fin N => P)`. The solution is a map `θstar` with `θstar ω` the solution of the program for every sample. The book glosses over measurability (p. 33); here the constraint relation $\{(\theta,\delta):\theta\in\Theta_\delta\}$ is assumed jointly measurable and `θstar` measurable. The ranges $\varepsilon\in[0,1]$ and $d\ge1$, implicit on the page, are explicit hypotheses. $N-i$ is natural-number subtraction with $i<d\le N$, so no truncation occurs. The probability is compared in $[0,\infty]$ with `ENNReal.ofReal` of the right-hand side.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 39, Theorem 3.7, Eq. (3.4)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

namespace ScenarioApproach.Generalization

/-- Theorem 3.7 (p. 39): for `N ≥ d`, under Assumptions 3.4 and 3.6,
`ℙ^N{V(θ*) > ε} ≤ ∑_{i=0}^{d-1} (N choose i) ε^i (1-ε)^{N-i}`. -/
theorem violation_tail_le_binomial_sum
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
    (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P) {ω | ε < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal
        (∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Generalization
