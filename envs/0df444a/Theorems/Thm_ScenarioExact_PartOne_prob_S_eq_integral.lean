-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_prob_S_eq_integral
-- name    : ScenarioExact.PartOne.prob_S_eq_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:24:10.630485+00:00
-- url     : https://prove2.me/theorems/baf5af1f-d415-4275-aa19-d5b01e3397fc
-- title:
--   (3.3), p. 8 — $\mathbb P^m\{S_{\mathcal I}\}=\int_0^1(1-\alpha)^{m-d}F(\mathrm d\alpha)$
-- statement:
--   Let $(\Delta,\mathcal D,\mathbb P)$ be a probability space and consider the uncertain program (1.1) with $c\in\mathbb R^d$, convex closed $\mathcal X$ and convex closed $\mathcal X_\delta$, such that every finite instance $P_k$ has a unique solution $x^*_k$, and assume the problem is fully-supported. Let $F(\alpha)=\mathbb P^d\{V(x^*_d)\le\alpha\}$ be the distribution of the violation of $x^*_d$, as in (3.1). Then for every $m\ge d$ and every set $\mathcal I\subseteq\{1,\dots,m\}$ of cardinality $d$,
--   $$\mathbb P^m\{S_{\mathcal I}\}=\int_0^1(1-\alpha)^{m-d}\,F(\mathrm d\alpha),\tag{3.3}$$
--   where $S_{\mathcal I}$ is the set of multi-extractions whose support constraints have exactly the indexes in $\mathcal I$.
--
--   Since the $\binom md$ sets $S_{\mathcal I}$ partition $\Delta^m$ up to a null set, (3.3) yields the moment identities (3.4) that determine $F$.
--
--   **Formalization Note.** The integral is the lower Lebesgue integral of $\alpha\mapsto(1-\alpha)^{m-d}$ (as an extended nonnegative real) over $[0,1]$ against the law $F$ (`violationLaw`); $F$ is concentrated on $[0,1]$, so this is the paper's $\int_0^1\cdots F(\mathrm d\alpha)$, atom at $0$ included. The statement is for every $\mathcal I$ of cardinality $d$, as printed. No measurability of $S_{\mathcal I}$ is assumed: the left side is the outer measure, and the paper's "measurability ... is assumed for granted" (p. 4) is replaced by the joint measurability of $\{(x,\delta): x\in\mathcal X_\delta\}$ and the measurability of the solution maps. Existence and uniqueness are assumed for every number of constraints, with the solution family `θs`; the nonempty-interior clause of Assumption 1 is not used and not assumed. Indexes are 0-based.
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, p. 8, eq. (3.3) (with (3.1), p. 7)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- (3.3), p. 8: for a fully-supported problem, `m ≥ d` and every index set `𝓘` of
cardinality `d`, `ℙ^m{S_𝓘} = ∫_0^1 (1 − α)^{m−d} F(dα)`, with `F` the law (3.1). -/
theorem prob_S_eq_integral
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
    {m : ℕ} (hm : d ≤ m) (I : Finset (Fin m)) (hI : I.card = d) :
    Measure.pi (fun _ : Fin m => P) (S c Θ Θδ θs I) =
      ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂(violationLaw P Θδ θs) := by sorry

end ScenarioExact.PartOne
