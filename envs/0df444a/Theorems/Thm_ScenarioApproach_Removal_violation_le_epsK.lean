-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_violation_le_epsK
-- name    : ScenarioApproach.Removal.violation_le_epsK
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:45.904125+00:00
-- url     : https://prove2.me/theorems/f1d2b9f6-163a-4b9a-93ae-e0969400b8d7
-- title:
--   Theorem 1.2 — with probability $\ge 1-\beta$, $V(\theta^*_k) \le \varepsilon_k$
-- statement:
--   Consider the convex scenario program with $d \ge 1$ decision variables and $N \ge d$ independent constraints, under Assumptions 3.4 and 3.6. Let an arbitrary removal procedure discard, as a function of the sample, $k$ constraints with $1 \le k \le N$, and let $\theta^*_k$ be the solution of the program without them, where the procedure ensures that $\theta^*_k$ violates every discarded constraint. Let $\beta \in (0,1)$ and let $\varepsilon_k$ be given by (1.9). Then
--
--   $$
--   \mathbb P^N\{V(\theta^*_k) \le \varepsilon_k\} \ge 1 - \beta,
--   $$
--
--   that is, with probability at least $1-\beta$ the solution obtained after discarding $k$ constraints has violation probability at most $\varepsilon_k$.
--
--   The level $\varepsilon_k$ is the empirical risk $k/N$ plus a margin of order $\ln N/\sqrt N$ when $k/N$ is held fixed, so discarding scenarios improves the cost while the guarantee degrades only slightly beyond the empirical risk.
--
--   **Formalization Note** The book states Theorem 1.2 for the loss-function formulation of Chapter 1 and notes (p. 20) that it generalizes to the constraint formulation; this is the constraint formulation, with the hypotheses of Theorem 3.9 (from which the book derives it in Section 3.3.1): $N \ge d$, Assumptions 3.4 and 3.6, and the discarded constraints violated (footnote 5), with probability one as in the proof of Theorem 3.9 (p. 65). The formula (1.9) divides by $\sqrt k$, so $k \ge 1$ (the book's remark (iv) on $k = 0$ does not apply to the formula as printed). Measurability is explicit: jointly measurable constraint relation, measurable solution maps of the scenario programs, measurable $\theta^*_k$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 18, Theorem 1.2 and Eq. (1.9); p. 17, footnote 5; p. 20 (generalization to the constraint setup); pp. 47–48, Section 3.3.1

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram
import Definitions.Def_ScenarioApproach_Removal_epsK

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_le_epsK {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexClosedConstraints Θ Θδ)
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (hsol_meas : ∀ (m : ℕ) (θs : (Fin m → Δ) → EuclideanSpace ℝ (Fin d)),
      (∀ ω, IsSolution Θ Θδ c ω (θs ω)) → Measurable θs)
    (hd : 1 ≤ d) (hN : d ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (hθk_meas : Measurable θk)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal (1 - β) ≤
      Measure.pi (fun _ : Fin N => P) {ω | ScenarioApproach.Generalization.violation P Θδ (θk ω) ≤ epsK N k d β} := by sorry

end ScenarioApproach.Removal
