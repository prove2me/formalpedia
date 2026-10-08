-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_violation_tail_le_binomial_sum
-- name    : ScenarioApproach.Removal.violation_tail_le_binomial_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:54:52.200647+00:00
-- url     : https://prove2.me/theorems/c5376218-683d-42c8-a054-73aa0cb99af4
-- title:
--   Theorem 3.7 — $\mathbb P^N\{V(\theta^*) > \varepsilon\} \le \sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}$
-- statement:
--   Consider the convex scenario program with $d \ge 1$ decision variables and $N \ge d$ constraints $\theta \in \Theta_{\delta_i}$, where $\delta_1,\dots,\delta_N$ are independent draws from a probability $\mathbb P$ on $\Delta$, and let $\theta^*$ be its solution. Suppose Assumption 3.4 ($\Theta$ and all $\Theta_\delta$ convex and closed) and Assumption 3.6 (for every $m$ and every sample of size $m$ the solution exists and is unique) hold. Then for every $\varepsilon \in [0,1]$
--
--   $$
--   \mathbb P^N\{V(\theta^*) > \varepsilon\} \le \sum_{i=0}^{d-1} \binom{N}{i} \varepsilon^i (1-\varepsilon)^{N-i},
--   $$
--
--   where $V$ is the violation probability of Definition 3.1 and $\mathbb P^N$ the product probability of the sample.
--
--   This is the generalization theorem of the scenario approach. In the constraint-removal setting it is applied to the program with the $N-k$ constraints that are kept, and it provides the distribution bound on which the proof of Theorem 3.9 rests.
--
--   **Formalization Note** The solution is a map $\theta^* : \Delta^N \to \mathbb R^d$ that is a solution of the program for every sample. The implicit measurability of the book (p. 33) is made explicit: the constraint relation $\{(\theta,\delta) : \theta \in \Theta_\delta\}$ is jointly measurable and $\theta^*$ is measurable. The ranges $1 \le d$ and $\varepsilon \in [0,1]$ are the book's implicit conventions. This statement duplicates the goal of the sibling mission on Theorem 3.7 in this mission's namespace.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 39, Theorem 3.7, Eq. (3.4)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_tail_le_binomial_sum {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexClosedConstraints Θ Θδ)
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (hd : 1 ≤ d) (hN : d ≤ N)
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution Θ Θδ c ω (θstar ω))
    (hθstar_meas : Measurable θstar)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P) {ω | ε < ScenarioApproach.Generalization.violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal (∑ i ∈ Finset.range d,
        (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Removal
