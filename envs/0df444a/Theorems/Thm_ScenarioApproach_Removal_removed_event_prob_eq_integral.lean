-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_removed_event_prob_eq_integral
-- name    : ScenarioApproach.Removal.removed_event_prob_eq_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:13.662524+00:00
-- url     : https://prove2.me/theorems/beb74ff2-aa9b-4bf4-9652-492e55163792
-- title:
--   Eq. (5.13) — $\mathbb P^N\{\Delta^N_I,\ V(\theta^*_I) > \varepsilon\} = \int_{(\varepsilon,1]} \alpha^k F_V(d\alpha)$
-- statement:
--   Fix a set $I$ of $k$ indexes from $\{1,\dots,N\}$ and let $\theta^*_I$ be the solution of the scenario program without the constraints with index in $I$ (Eq. (5.9)). Let $\Delta^N_I$ be the set of samples for which $\theta^*_I$ violates all the removed constraints $\theta \in \Theta_{\delta_i}$, $i \in I$, and let $F_V$ be the distribution of the random variable $V(\theta^*_I)$ under $\mathbb P^N$. Under Assumption 3.6, for every $\varepsilon \in [0,1]$,
--
--   $$
--   \mathbb P^N\{(\delta_1,\dots,\delta_N) \in \Delta^N_I : V(\theta^*_I) > \varepsilon\} = \int_{(\varepsilon,1]} \alpha^k \, F_V(d\alpha).
--   $$
--
--   Conditionally on the kept scenarios, each of the $k$ removed scenarios independently produces a constraint violated by $\theta^*_I$ with probability $V(\theta^*_I)$; the identity expresses this in integrated form and is the second step of the proof of Theorem 3.9.
--
--   **Formalization Note** $F_V$ is the push-forward of $\mathbb P^N$ under $\omega \mapsto V(\theta^*_I(\omega))$ (`Measure.map`), and the integral is a lower Lebesgue integral of $\alpha^k$ over $(\varepsilon,1]$. Measurability is explicit: the constraint relation is jointly measurable and $\theta^*_I$ is measurable. $\theta^*_I$ is any map that is a solution of the reduced program for every sample; Assumption 3.6 makes it depend only on the kept scenarios.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 65, Eq. (5.13); p. 64, Eqs. (5.9)–(5.10)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem removed_event_prob_eq_integral {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (J : Finset (Fin N)) (hJ : J.card = k)
    (θJ : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθJ : ∀ ω, IsSolutionWithout Θ Θδ c ω J (θJ ω))
    (hθJ_meas : Measurable θJ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P)
        {ω | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θJ ω)} =
      ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k)
        ∂(Measure.map (fun ω => ScenarioApproach.Generalization.violation P Θδ (θJ ω)) (Measure.pi (fun _ : Fin N => P))) := by sorry

end ScenarioApproach.Removal
