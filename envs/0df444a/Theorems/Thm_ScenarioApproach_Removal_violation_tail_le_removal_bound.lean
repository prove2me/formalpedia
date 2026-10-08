-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_violation_tail_le_removal_bound
-- name    : ScenarioApproach.Removal.violation_tail_le_removal_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:53.989975+00:00
-- url     : https://prove2.me/theorems/7258f3c6-4058-463c-b2ca-7ae0d5d577aa
-- title:
--   Theorem 3.9 — $\mathbb P^N\{V(\theta^*_k) > \varepsilon\} \le \binom{k+d-1}{k}\sum_{i=0}^{k+d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}$
-- statement:
--   Consider the convex scenario program
--
--   $$
--   \min_{\theta\in\Theta} c^{\mathsf T}\theta \quad \text{subject to } \theta \in \bigcap_{i=1,\dots,N} \Theta_{\delta_i}
--   $$
--
--   with $d \ge 1$ decision variables and $N \ge d$ constraints, where $\delta_1,\dots,\delta_N$ are independent draws from a probability $\mathbb P$ on $\Delta$. Assume Assumption 3.4 ($\Theta$ and every $\Theta_\delta$ are convex and closed) and Assumption 3.6 (for every $m$ and every sample of size $m$ the solution exists and is unique).
--
--   Let an arbitrary removal procedure select, as a function of the sample, a set of $k \le N$ constraints, and let $\theta^*_k$ be the solution of the program without these constraints, where the procedure ensures that $\theta^*_k$ violates exactly the $k$ removed constraints (a removed constraint that is satisfied is reinstated and another one removed). Then for every $\varepsilon \in [0,1]$
--
--   $$
--   \mathbb P^N\{V(\theta^*_k) > \varepsilon\} \le \binom{k+d-1}{k} \sum_{i=0}^{k+d-1} \binom Ni \varepsilon^i (1-\varepsilon)^{N-i},
--   $$
--
--   where $V$ is the violation probability of Definition 3.1.
--
--   The bound does not depend on how the constraints are chosen for removal: optimal, greedy and random removal all enjoy the same guarantee. For $k = 0$ it reduces to Theorem 3.7.
--
--   **Formalization Note** The removal procedure is a map $I$ from samples to $k$-element index sets, arbitrary otherwise; $\theta^*_k$ is a map that, for every sample, solves the program without the constraints in $I$, and it violates each removed constraint with probability one (the book's "θ*_k violates k constraints with probability 1", p. 65; requiring it for every sample would be unsatisfiable for $1 \le k < N$, because on a sample with all $\delta_i$ equal a kept constraint coincides with a removed one). Measurability, which the book glosses over (p. 33), is explicit: the constraint relation $\{(\theta,\delta):\theta\in\Theta_\delta\}$ is jointly measurable, the solution map of the scenario program with $m$ constraints is measurable for every $m$, and $\theta^*_k$ is measurable. The ranges $d \ge 1$, $k \le N$ and $\varepsilon \in [0,1]$ are the book's implicit conventions. When $k+d-1 \ge N$ the sum equals $1$ and the bound is trivial, as in the book.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 45, Theorem 3.9, Eq. (3.13); pp. 44–45 (definition of θ*_k)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_tail_le_removal_bound {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexClosedConstraints Θ Θδ)
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (hsol_meas : ∀ (m : ℕ) (θs : (Fin m → Δ) → EuclideanSpace ℝ (Fin d)),
      (∀ ω, IsSolution Θ Θδ c ω (θs ω)) → Measurable θs)
    (hd : 1 ≤ d) (hN : d ≤ N) (hkN : k ≤ N)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (hθk_meas : Measurable θk)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P) {ω | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} ≤
      ENNReal.ofReal (((k + d - 1).choose k : ℝ) *
        ∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Removal
