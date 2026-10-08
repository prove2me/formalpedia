-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_choose_mul_integral_eq_one
-- name    : ScenarioExact.PartOne.choose_mul_integral_eq_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:24:05.875875+00:00
-- url     : https://prove2.me/theorems/00825a3d-2a47-4e4e-8a29-707594ea3e2a
-- title:
--   (3.4), p. 8 — $\binom md\int_0^1(1-\alpha)^{m-d}F(\mathrm d\alpha)=1$ for all $m\ge d$
-- statement:
--   Under the hypotheses of (3.3) — a probability space $(\Delta,\mathcal D,\mathbb P)$, convex closed $\mathcal X$ and $\mathcal X_\delta$, a unique solution $x^*_k$ of every finite instance $P_k$, and a fully-supported problem — let $F$ be the distribution (3.1) of the violation of $x^*_d$. Then
--   $$\binom md\int_0^1(1-\alpha)^{m-d}\,F(\mathrm d\alpha)=1,\qquad\forall m\ge d.\tag{3.4}$$
--
--   The paper obtains (3.4) from (3.3), the partition of $\Delta^m$ (up to a null set) into the $\binom md$ sets $S_{\mathcal I}$, and $\mathbb P^m\{\Delta^m\}=1$. As $m$ ranges over $m\ge d$, (3.4) prescribes every moment of $1-\alpha$ under $F$, which is the moment problem solved by the next milestone.
--
--   **Formalization Note.** The integral is the lower Lebesgue integral over $[0,1]$ against `violationLaw`, and the identity is an equality of extended nonnegative reals. Measurability is entered as the joint measurability of the constraint relation and of the solution maps; existence and uniqueness for every number of constraints, with the solution family `θs`.
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, p. 8, eq. (3.4)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- (3.4), p. 8: for a fully-supported problem,
`binom(m, d) ∫_0^1 (1 − α)^{m−d} F(dα) = 1` for every `m ≥ d`. -/
theorem choose_mul_integral_eq_one
    {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    -- Assumption 1 / (1.1): `𝒳` and every `𝒳_δ` are convex and closed
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    -- Assumption 1: for every number `k` of constraints and every sample, `P_k` has a unique solution
    (hexu : ∀ (k : ℕ) (ω : Fin k → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    -- measurability ("assumed for granted", p. 4): the constraint relation is jointly measurable
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    -- `θs k ω` is the solution `x*_k` of `P_k` with the sampled constraints `ω`; measurable in `ω`
    (θs : (k : ℕ) → (Fin k → Δ) → EuclideanSpace ℝ (Fin d))
    (hθs : ∀ (k : ℕ) (ω : Fin k → Δ), IsSolution c Θ Θδ ω (θs k ω))
    (hθs_meas : ∀ k, Measurable (θs k))
    -- Definition 2.3: the problem is fully-supported
    (hfs : FullySupported c Θ Θδ P) :
    ∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂(violationLaw P Θδ θs) =
        1 := by sorry

end ScenarioExact.PartOne
