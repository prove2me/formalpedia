-- Prove2me | Theorems.Thm_ResolvingPricing_theorem_3
-- name    : ResolvingPricing.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:33.188186+00:00
-- url     : https://prove2.me/theorems/8364a24b-9f20-4929-94f7-405cf0d032aa
-- title:
--   Theorem 3: the resolving heuristic has constant regret
-- statement:
--   Consider the single-product model under Assumptions A1–A5 and let the normalized initial inventory satisfy $x_T\in(\underline d,\lambda^u)$ (limited inventory). Then there is a constant $K$, depending on the model and on $x_T$ but not on the horizon, such that for every $T\ge1$, every run $\rho$ following the resolving heuristic $\pi^r$ and every admissible run $\pi$,
--   $$R^{\pi^r}(T,x_T)\ \ge\ R^{\pi}(T,x_T)-K.$$
--   In the paper's words, $R^{\pi^r}(T,x_T)\ge R^{\pi^*}(T,x_T)-O(1)$: the regret of the resolving heuristic against the optimal dynamic pricing policy is bounded by a constant independent of $T$.
--
--   Earlier analyses compared the resolving heuristic with the fluid upper bound and obtained regret $O(\ln T)$; Theorem 4 of the paper shows that comparison cannot give a constant, which is why the theorem compares with the optimal policy directly.
--
--   **Formalization Note** The two runs may live on different probability spaces, in arbitrary universes.
--
--   Differences from the source:
--   - reading: A4: the conditional distribution of ξ_t given p_t is Q(p_t) → the conditional law of ξ_t given the past ℱ_{t+1} is Q(p_t) (condExp of indicators of Borel sets); reason: the Bellman equation (5) and the recursion (7), p.3543, take the expectation over ξ ~ Q(price) given the current state, and the network analogue B4 (p.3549) states independence from past noise; under the weaker reading Q does not determine R^π(T, x_T)
--   - reading: demand d_t = λ_t + ξ_t enters (1) as the bound 0 ≤ s ≤ d_t → 0 ≤ λ + ξ for Q(λ)-almost every ξ, λ ∈ [d̲, d̄]; reason: (1) requires nonnegative demand, and Lemma 2's proof uses nonnegative revenue (p.3555)
--   - encoding: prices p ∈ [p̲, p̄] with demand f(p) and noise law Q(p) → demand rates λ ∈ [d̲, d̄] with price g(λ) = f⁻¹(λ) and noise law Q(λ) := Q(f⁻¹(λ)); |f(p) − f(p′)| = |λ − λ′| in A5; reason: the paper's own parametrization in (5); f is a bijection [p̲, p̄] → [d̲, d̄], so the instances are the same
--   - encoding: A1: f strictly decreasing on [p̲, p̄] with values in ℝ₊, prices in 𝒫 ⊂ ℝ₊, p̄ ≤ +∞ → 0 ≤ d̲ < d̄, g ≥ 0 on [d̲, d̄], g strictly decreasing on (d̲, d̄]; reason: with p̄ = +∞ the price at d̲ is not a real number; when d̲ > 0 the value g(d̲) is pinned by the continuity of r at d̲, and when d̲ = 0 it enters only through r(0) = 0; A4, A5 and demand ≥ 0 are also required of Q(d̲), which excludes no model (when p̄ = +∞, Q(p) converges in 𝒲₂ as p → ∞ by A5, and the limit satisfies them)
--   - encoding: r′, r″, r‴ exist on [d̲, d̄] (A2, A3) → r, r′, r″ differentiable within [d̲, d̄]; r′, r″, r‴ are iteratedDerivWithin on [d̲, d̄] (one-sided at the endpoints); reason: the derivatives of a function defined on a closed interval
--   - encoding: 𝒲₂(Q, Q′) = inf_Ξ √(𝔼|ξ − ξ′|²) → WassersteinDRO.StrongDuality.wasserstein 2 = (inf over couplings of ∫|ξ − ξ′|²)^{1/2} in ℝ≥0∞, compared with ofReal(L|λ − λ′|); reason: the square root is increasing and continuous, so it commutes with the infimum; same values
--   - encoding: λᵘ := argmax_{λ≥0} r(λ), rᵘ := max_{λ≥0} r(λ) (p.3541) → λᵘ is a datum of the model with IsMaxOn r [d̲, d̄] λᵘ and λᵘ ∈ (d̲, d̄); rᵘ = r(λᵘ); reason: r is defined only on [d̲, d̄] (Table 1, p.3542, writes argmax over [d̲, d̄]); the maximizer is unique by strict concavity
--   - generalization: the resolving heuristic prices at f⁻¹(min{x_t, λᵘ}) and is defined for x_t ≥ d̲ only → a resolving run chooses min{x_t, λᵘ} whenever x_t ≥ d̲ and any admissible demand rate when x_t < d̲; reason: the statement holds for every such choice; for d̲ = 0 the case never arises, and the paper's πʳ is one of these runs
--   - generalization: the optimal dynamic pricing policy π* (value φ*_T(x_T) = R^{π*}(T, x_T)) → every admissible run π (demand rates ℱ_{t+1}-measurable, possibly randomized); reason: R^{π*} = sup_π R^π, so the statement for every π implies the paper's and needs no optimal policy to exist; the paper's Markov policies π_t(y_t) are admissible runs
--   - encoding: R^{πʳ}(T, x_T) ≥ R^{π*}(T, x_T) − O(1) for T ≥ 1 → ∃ K, ∀ T ≥ 1, ∀ runs: R^π − K ≤ R^{πʳ}, with K chosen before T and the runs; reason: O(1) is "a constant that is independent of T" (pp.3539–3540) that "depends on the shape of the demand function" and on x_T (p.3554)
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §3.1, Theorem 3, p.3541 (PDF p.5); proof §4.2, pp.3544–3547, with Lemmas 1–2 (Appendix A, pp.3554–3555)

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

namespace ResolvingPricing

universe u v

/-- **Theorem 3 (constant regret of the resolving heuristic)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3541:
"Suppose x_T ∈ (d̲, λᵘ). Let πʳ be the resolving heuristic and π* be the optimal policy. For T ≥ 1,
it holds that R^{πʳ}(T, x_T) ≥ R^{π*}(T, x_T) − O(1)."

For every model satisfying A1–A5 and every initial normalized inventory `x_T ∈ (d̲, λᵘ)` there is a
constant `K`, independent of the horizon, such that for every `T ≥ 1`, every resolving run `ρ` and
every admissible run `π` (each on its own probability space and filtration),
`R^π(T, x_T) − K ≤ R^{πʳ}(T, x_T)`.

**Formalization Note.** `O(1)` is `∃ K` placed before `T` and before both runs, so `K` depends only
on the model and `x_T`. The optimal policy `π*` is replaced by every admissible run: since
`R^{π*} = sup_π R^π`, the two statements are equivalent, and no optimal policy needs to exist. A
resolving run may do anything admissible when its normalized inventory falls below `d̲` (where the
paper leaves `πʳ` undefined); `K` is uniform over these choices. The sample spaces live in arbitrary
universes `u`, `v`. -/
theorem theorem_3 (P : Model) (hP : P.Assumptions) (x : ℝ) (hx : x ∈ Set.Ioo P.dlo P.lamU) :
    ∃ K : ℝ, ∀ T : ℕ, 1 ≤ T →
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ mΩ) (ρ : Run P T x μ ℱ), ρ.IsResolving →
      ∀ (Ω' : Type v) [mΩ' : MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
        (ℱ' : Filtration ℕ mΩ') (π : Run P T x μ' ℱ'),
        π.expRevenue - K ≤ ρ.expRevenue := by sorry

end ResolvingPricing
