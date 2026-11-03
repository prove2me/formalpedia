-- Prove2me | Theorems.Thm_ResolvingPricing_lemma_1
-- name    : ResolvingPricing.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:28.58394+00:00
-- url     : https://prove2.me/theorems/d87f6241-0f5e-4a93-ae82-265ed00289f8
-- title:
--   Lemma 1: $\mathbb E[T^\sharp]$ is bounded independently of $T$
-- statement:
--   Let $x_T\in(\underline d,\lambda^u)$ and $T\ge1$, and let $T^\sharp$ be the time (8) built from the noises of a run following the resolving heuristic. Then
--   $$\mathbb E[T^\sharp]\le 2+\frac{2|r''(x_T)|B_\xi}{r'(x_T)}+\frac{4B_\xi^4}{\min\{x_T-\underline d,\ \lambda^u-x_T,\ -r'(x_T)/(2r''(x_T))\}^4}.$$
--
--   The bound does not depend on the horizon $T$; it is what turns the regret bound (26) into a constant.
--
--   **Formalization Note** $\mathbb E[T^\sharp]$ is the integral of the bounded random variable $T^\sharp\le T+1$.
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
--   - encoding: T♯ := max{τ ≥ 1 : |ξ̄ʳ→τ−1| > γ} ∨ ⌈2|r″(x_T)|B_ξ/r′(x_T) + 1⌉ (8) → the maximum runs over 2 ≤ τ ≤ T (empty maximum 0); ceilings are Nat.ceil; reason: τ = 1 would involve ξ̄→0, which contains ξ_1/0, and never changes T♯ because the second term is at least 1
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4, Lemma 1, Eq. (10), p.3544 (PDF p.8); proof in Appendix A, p.3554

import Mathlib
import Definitions.Def_ResolvingPricing_Tsharp

open MeasureTheory

namespace ResolvingPricing

/-- **Lemma 1**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3544: "For x_T ∈ (d̲, λᵘ) and any T ≥ 1, it holds that
𝔼[T♯] ≤ 2 + 2|r″(x_T)|B_ξ/r′(x_T) + 4B_ξ⁴/min{x_T − d̲, λᵘ − x_T, −r′(x_T)/2r″(x_T)}⁴." (10)

Here `T♯` is the time of (8) computed from the noises of a resolving run.

**Formalization Note.** `𝔼[T♯]` is the integral of the bounded random variable `T♯ ≤ T + 1`.
`−r′(x_T)/2r″(x_T)` is read as `−r′(x_T)/(2r″(x_T))`. -/
theorem lemma_1 (P : Model) (hP : P.Assumptions) (x : ℝ) (hx : x ∈ Set.Ioo P.dlo P.lamU) (T : ℕ)
    (hT : 1 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ρ : Run P T x μ ℱ) (hρ : ρ.IsResolving) :
    ∫ ω, (ρ.Tsharp ω : ℝ) ∂μ ≤ 2 + 2 * |P.r2 x| * P.Bξ / P.r1 x
      + 4 * P.Bξ ^ 4 / (min (min (x - P.dlo) (P.lamU - x)) (-P.r1 x / (2 * P.r2 x))) ^ 4 := by sorry

end ResolvingPricing
