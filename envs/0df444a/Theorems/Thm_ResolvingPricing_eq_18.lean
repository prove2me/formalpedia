-- Prove2me | Theorems.Thm_ResolvingPricing_eq_18
-- name    : ResolvingPricing.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:38.283579+00:00
-- url     : https://prove2.me/theorems/7aaac0ee-98d8-4279-a4ae-5de5eaeb8b9f
-- title:
--   Eq. (18): optional stopping for the term $\mathcal B$
-- statement:
--   Let $x_T\in(\underline d,\lambda^u)$ and $T\ge1$. Let $\rho$ be a run following the resolving heuristic, with noises $\xi^r_\tau$ and time $T^\sharp$ of (8), and let $\pi$ be any admissible run on the same filtered probability space, with normalized inventories $x^*_\tau$ and $\Delta_\tau=\lambda^*_\tau-x^*_\tau$. Put $\eta=-(x^*_{T^\sharp-1}-\lambda^u)^+$ and
--   $$\mathcal B=\sum_{\tau=T^\sharp}^T\bar\xi^r_{\to\tau}[\Delta_\tau-\bar\Delta_{\to\tau}]-(T^\sharp-1)\bar\xi^r_{\to T^\sharp-1}\bar\Delta_{\to T^\sharp-1}+(T^\sharp-1)\bar\xi^r_{\to T^\sharp-1}\eta.$$
--   Then
--   $$\mathbb E[\mathcal B]=\mathbb E\big[(T^\sharp-1)\,\bar\xi^r_{\to T^\sharp-1}\,\eta\big].$$
--
--   This removes the term $\mathcal B$ of the regret decomposition (16) up to a quantity controlled by $\eta$.
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
--   - encoding: T♯ := max{τ ≥ 1 : |ξ̄ʳ→τ−1| > γ} ∨ ⌈2|r″(x_T)|B_ξ/r′(x_T) + 1⌉ (8) → the maximum runs over 2 ≤ τ ≤ T (empty maximum 0); ceilings are Nat.ceil; reason: τ = 1 would involve ξ̄→0, which contains ξ_1/0, and never changes T♯ because the second term is at least 1
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.2, Eq. (18), p.3545 (PDF p.9); ℬ and η defined on pp.3544–3545

import Mathlib
import Definitions.Def_ResolvingPricing_Tsharp

open MeasureTheory

namespace ResolvingPricing

/-- **Eq. (18)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3545: with
`ℬ = ∑_{τ=T♯}^T ξ̄ʳ→τ[Δ_τ − Δ̄→τ] − (T♯ − 1)ξ̄ʳ→T♯−1 Δ̄→T♯−1 + (T♯ − 1)ξ̄ʳ→T♯−1 η` and
`η = −(x*_{T♯−1} − λᵘ)⁺` (p.3544), "By Doob's optional stopping theorem, we have
𝔼[−∑_{τ=T♯}^T ξʳ_τ Δ̄→τ−1] = 0, and thus, 𝔼[ℬ] = 𝔼[(T♯ − 1)ξ̄ʳ→T♯−1 η]."

Here `ρ` is a resolving run (its noises `ξʳ` define `T♯`) and `π` is any admissible run on the same
filtered probability space (its `Δ_τ = λ*_τ − x*_τ` and `x*` enter `ℬ` and `η`).

**Formalization Note.** The paper's `π*` is generalized to every admissible run sharing the filtration
of `ρ`. At `T♯ = 1` the factor `T♯ − 1` is `0`. -/
theorem eq_18 (P : Model) (hP : P.Assumptions) (x : ℝ) (hx : x ∈ Set.Ioo P.dlo P.lamU) (T : ℕ)
    (hT : 1 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ρ π : Run P T x μ ℱ) (hρ : ρ.IsResolving) :
    let ξr : Ω → ℕ → ℝ := fun ω t => ρ.xiB t ω
    let Δ : Ω → ℕ → ℝ := fun ω t => π.DeltaB t ω
    let η : Ω → ℝ := fun ω => -max (π.xB (ρ.Tsharp ω - 1) ω - P.lamU) 0
    ∫ ω, (∑ τ ∈ Finset.Icc (ρ.Tsharp ω) T, harm T (ξr ω) τ * (Δ ω τ - harm T (Δ ω) τ)
        - ((ρ.Tsharp ω : ℝ) - 1) * harm T (ξr ω) (ρ.Tsharp ω - 1) * harm T (Δ ω) (ρ.Tsharp ω - 1)
        + ((ρ.Tsharp ω : ℝ) - 1) * harm T (ξr ω) (ρ.Tsharp ω - 1) * η ω) ∂μ
      = ∫ ω, ((ρ.Tsharp ω : ℝ) - 1) * harm T (ξr ω) (ρ.Tsharp ω - 1) * η ω ∂μ := by sorry

end ResolvingPricing
