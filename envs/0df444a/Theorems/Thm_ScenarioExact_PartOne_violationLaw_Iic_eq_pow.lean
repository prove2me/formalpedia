-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_violationLaw_Iic_eq_pow
-- name    : ScenarioExact.PartOne.violationLaw_Iic_eq_pow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:24:36.226921+00:00
-- url     : https://prove2.me/theorems/5886a9e0-6270-4a73-bb13-dde187b37f51
-- title:
--   (3.2), p. 7 — the violation of $x^*_d$ has distribution $F(\alpha)=\alpha^d$
-- statement:
--   Let $(\Delta,\mathcal D,\mathbb P)$ be a probability space and consider the uncertain program (1.1) with $c\in\mathbb R^d$, $d\ge1$, convex closed $\mathcal X$ and convex closed $\mathcal X_\delta$, such that every finite instance $P_k$ has a unique solution $x^*_k$, and assume the problem is fully-supported. Let $F(\alpha)=\mathbb P^d\{V(x^*_d)\le\alpha\}$ be the distribution (3.1) of the violation of the solution with $d$ random constraints. Then
--   $$F(\alpha)=\alpha^d\qquad\text{for every }\alpha\in[0,1],\tag{3.2}$$
--   independently of the problem type.
--
--   This is the key fact of PART 1: the law of $V(x^*_d)$ is the same for every fully-supported problem. The final computation of PART 1 integrates against it to obtain (2.3).
--
--   **Formalization Note.** $F(\alpha)$ is `violationLaw P Θδ θs (Set.Iic α)`, an extended nonnegative real, compared with $\alpha^d$ through `ENNReal.ofReal`; values of $\alpha$ outside $[0,1]$ are not claimed (there $F$ is $0$ or $1$). Measurability is entered as the joint measurability of the constraint relation and of the solution maps; existence and uniqueness for every number of constraints, with the solution family `θs`.
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, p. 7, eq. (3.2) (with (3.1))

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- (3.2), p. 7: for a fully-supported problem the distribution of the violation of `x*_d`
is `F(α) = α^d` on `[0, 1]`. -/
theorem violationLaw_Iic_eq_pow
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
    (hfs : FullySupported c Θ Θδ P)
    (hd : 1 ≤ d) :
    ∀ α ∈ Set.Icc (0 : ℝ) 1, violationLaw P Θδ θs (Set.Iic α) = ENNReal.ofReal (α ^ d) := by sorry

end ScenarioExact.PartOne
