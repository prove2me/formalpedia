-- Prove2me | Theorems.Thm_ResolvingPricing_lemma_2
-- name    : ResolvingPricing.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:52.762201+00:00
-- url     : https://prove2.me/theorems/be3a0658-6b31-48c3-87f5-ac057c00962a
-- title:
--   Lemma 2: revenue bounds through $T^\sharp$ (corrected: $r$ below $\underline d$)
-- statement:
--   Let $x_T\in(\underline d,\lambda^u)$ and $T\ge1$. Let $\rho$ be a run following the resolving heuristic, with normalized inventories $x^r_\tau$ and time $T^\sharp$ of (8), and let $\pi$ be any admissible run on the same filtered probability space, with normalized inventories $x^*_\tau$ and $\Delta_\tau=\lambda^*_\tau-x^*_\tau$. Write $\varphi^*_T(x_T)$ and $\varphi^r_T(x_T)$ for the expected revenues of $\pi$ and $\rho$. Then
--   1. $\displaystyle \varphi^*_T(x_T)\le\mathbb E\Big[\sum_{\tau=T^\sharp}^T r(x^*_\tau+\Delta_\tau)+(T^\sharp-1)\,\tilde r(x^*_{T^\sharp-1})\Big]$;
--   2. $\displaystyle \mathbb E\Big[\sum_{\tau=T^\sharp}^T r(x^r_\tau)\Big]-r^u\le\varphi^r_T(x_T)$;
--   3. $\displaystyle \varphi^r_T(x_T)\le\mathbb E\Big[\sum_{\tau=T^\sharp}^T r(x^r_\tau)+(T^\sharp-1)\,\tilde r(x^r_{T^\sharp-1})\Big]$,
--
--   where $\tilde r(x)=r(\min\{x,\lambda^u\})$ for $x\ge\underline d$ and $\tilde r(x)=x\,f^{-1}(\underline d)$ for $x<\underline d$.
--
--   The lemma reduces both expected revenues to sums of single-period revenue rates after $T^\sharp$ plus a fluid term for the remaining $T^\sharp-1$ periods.
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
--   - correction: (T♯ − 1) r(min{x_{T♯−1}, λᵘ}) → (T♯ − 1) r̃(x_{T♯−1}) with r̃(x) = r(min{x, λᵘ}) for x ≥ d̲ and r̃(x) = x f⁻¹(d̲) for x < d̲; reason: the printed term is undefined when x_{T♯−1} < d̲: in the §5 instance f(p) = 3/4 − p/2 on [0, 1] (d̲ = 1/4) a policy that sells out its 5T/16 units before period T♯ − 1 has x_{T♯−1} = 0 and r(0) = 0·f⁻¹(0) with 0 ∉ f([0, 1]); r̃ equals the printed term whenever it is defined (always when d̲ = 0)
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4, Lemma 2, p.3544 (PDF p.8); proof in Appendix A, pp.3554–3555

import Mathlib
import Definitions.Def_ResolvingPricing_Tsharp

open MeasureTheory

namespace ResolvingPricing

/-- **Lemma 2 (corrected: `r` below `d̲`)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3544: "Let x_T ∈ (d̲, λᵘ). Let T♯ be
the stopping time defined in Equation (8). Then, it holds that
φ*_T(x_T) ≤ 𝔼[∑_{τ=T♯}^T r(x*_τ + Δ_τ) + (T♯ − 1) r(min{x*_{T♯−1}, λᵘ})],
𝔼[∑_{τ=T♯}^T r(xʳ_τ)] − rᵘ ≤ φʳ_T(x_T) ≤ 𝔼[∑_{τ=T♯}^T r(xʳ_τ) + (T♯ − 1) r(min{xʳ_{T♯−1}, λᵘ})]."

For a resolving run `ρ` (which defines `T♯`) and any admissible run `π` on the same filtered
probability space, the three inequalities hold with `φ*_T(x_T)` the expected revenue of `π` and
`φʳ_T(x_T)` that of `ρ`, and with `r(min{x, λᵘ})` replaced by `r̃(x)` (`Model.rtilde`).

**Formalization Note.** Correction: `r(min{x, λᵘ})` evaluates `r = λ f⁻¹(λ)` outside its domain
`[d̲, d̄]` when `x < d̲` (possible when `d̲ > 0`, e.g. after a sell-out); `r̃(x) = x f⁻¹(d̲)` there and
`r̃(x) = r(min{x, λᵘ})` for `x ≥ d̲`. The paper's `π*` is generalized to every admissible run sharing
the filtration of `ρ`. At `T♯ = 1` the factor `T♯ − 1` is `0`. -/
theorem lemma_2 (P : Model) (hP : P.Assumptions) (x : ℝ) (hx : x ∈ Set.Ioo P.dlo P.lamU) (T : ℕ)
    (hT : 1 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ρ π : Run P T x μ ℱ) (hρ : ρ.IsResolving) :
    π.expRevenue ≤ ∫ ω, (∑ τ ∈ Finset.Icc (ρ.Tsharp ω) T, P.r (π.xB τ ω + π.DeltaB τ ω)
        + ((ρ.Tsharp ω : ℝ) - 1) * P.rtilde (π.xB (ρ.Tsharp ω - 1) ω)) ∂μ ∧
    (∫ ω, ∑ τ ∈ Finset.Icc (ρ.Tsharp ω) T, P.r (ρ.xB τ ω) ∂μ) - P.ru ≤ ρ.expRevenue ∧
    ρ.expRevenue ≤ ∫ ω, (∑ τ ∈ Finset.Icc (ρ.Tsharp ω) T, P.r (ρ.xB τ ω)
        + ((ρ.Tsharp ω : ℝ) - 1) * P.rtilde (ρ.xB (ρ.Tsharp ω - 1) ω)) ∂μ := by sorry

end ResolvingPricing
