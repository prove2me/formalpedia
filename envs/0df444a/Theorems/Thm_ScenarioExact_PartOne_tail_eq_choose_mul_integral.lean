-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_tail_eq_choose_mul_integral
-- name    : ScenarioExact.PartOne.tail_eq_choose_mul_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:24:32.020102+00:00
-- url     : https://prove2.me/theorems/5b7e448e-4bb1-4f0a-9442-416d733bb2d2
-- title:
--   §3, PART 1, pp. 8–9 — $\mathbb P^N\{V(x^*_N)>\varepsilon\}=\binom Nd\int_\varepsilon^1(1-\alpha)^{N-d}F(\mathrm d\alpha)$
-- statement:
--   Let $(\Delta,\mathcal D,\mathbb P)$ be a probability space and consider the uncertain program (1.1) with $c\in\mathbb R^d$, $d\ge1$, convex closed $\mathcal X$ and convex closed $\mathcal X_\delta$, such that every finite instance $P_k$ has a unique solution $x^*_k$, and assume the problem is fully-supported. Let $F$ be the distribution (3.1) of the violation of $x^*_d$ and $V$ the violation probability (Definition 1.1). Then for every $N\ge d$ and every $\varepsilon\in[0,1]$,
--   $$\mathbb P^N\{V(x^*_N)>\varepsilon\}=\binom Nd\int_{(\varepsilon,1]}(1-\alpha)^{N-d}\,F(\mathrm d\alpha).$$
--
--   The paper partitions the event $\{V(x^*_N)>\varepsilon\}$ according to the indexes of the $d$ support constraints. Combined with (3.2) and the integration-by-parts identity, this yields (2.3).
--
--   **Formalization Note.** The paper's $\int_\varepsilon^1\cdots F(\mathrm d\alpha)$ comes from the indicator of $\{\alpha>\varepsilon\}$, so it is taken over the half-open interval $(\varepsilon,1]$; $F$ may have an atom at $\varepsilon$ in this generality. The integral is the lower Lebesgue integral against `violationLaw`, and the identity is an equality of extended nonnegative reals. The solution of the program with $N$ constraints is `θs N`, which under existence and uniqueness is the goal theorem's `θstar`. Measurability of the event is not assumed; it follows from the joint measurability of the constraint relation and the measurability of the solution maps, which are assumed.
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, pp. 8–9, §3, PART 1, 'To conclude the proof of PART 1', first four lines of the display

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- §3, PART 1, pp. 8–9: for a fully-supported problem,
`ℙ^N{V(x*_N) > ε} = binom(N, d) ∫_ε^1 (1 − α)^{N−d} F(dα)`, the integral over `(ε, 1]`. -/
theorem tail_eq_choose_mul_integral
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
    {N : ℕ} (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P) {ω | ε < violation P Θδ (θs N ω)} =
      (N.choose d : ℝ≥0∞) *
        ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal ((1 - α) ^ (N - d)) ∂(violationLaw P Θδ θs) := by sorry

end ScenarioExact.PartOne
