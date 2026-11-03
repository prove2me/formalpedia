-- Prove2me | Theorems.Thm_ResolvingPricing_eq_13
-- name    : ResolvingPricing.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:42.66921+00:00
-- url     : https://prove2.me/theorems/9922f71e-aa5c-4174-b10f-adc4e83ae040
-- title:
--   Eq. (13): Taylor and strict-concavity bound on single-period revenue
-- statement:
--   Let $x_T\in(\underline d,\lambda^u)$, and let $\bar\Delta,\ \Xi^*,\ \Xi^r,\ \bar\ell\ge0,\ \Delta$ be real numbers (standing for $\bar\Delta_{\to\tau}$, $\bar\xi^*_{\to\tau}$, $\bar\xi^r_{\to\tau}$, $\bar\ell^*_{\to\tau}$, $\Delta_\tau$), such that $x_T-\bar\Delta-\Xi^*+\bar\ell+\Delta$, $x_T-\bar\Delta-\Xi^*+\Delta$ and $x_T-\Xi^r$ lie in $[\underline d,\bar d]$. With $E=\Delta-\bar\Delta+(\Xi^r-\Xi^*)$,
--   $$r(x_T-\bar\Delta-\Xi^*+\bar\ell+\Delta)-r(x_T-\Xi^r)\le r'(\underline d)\,\bar\ell+r'(x_T)E-r''(x_T)\,\Xi^r E+\frac M2|\Xi^r|^2|E|-\frac m2|E|^2.$$
--
--   By (6) and (9), the left side is $r(x^*_\tau+\Delta_\tau)-r(x^r_\tau)$ for $\tau\ge T^\sharp$; the bound is the first step of the comparison between the two policies.
--
--   **Formalization Note** $r'(\underline d)$ is the right derivative of $r$ at $\underline d$.
--
--   Differences from the source:
--   - reading: A4: the conditional distribution of ξ_t given p_t is Q(p_t) → the conditional law of ξ_t given the past ℱ_{t+1} is Q(p_t) (condExp of indicators of Borel sets); reason: the Bellman equation (5) and the recursion (7), p.3543, take the expectation over ξ ~ Q(price) given the current state, and the network analogue B4 (p.3549) states independence from past noise; under the weaker reading Q does not determine R^π(T, x_T)
--   - reading: demand d_t = λ_t + ξ_t enters (1) as the bound 0 ≤ s ≤ d_t → 0 ≤ λ + ξ for Q(λ)-almost every ξ, λ ∈ [d̲, d̄]; reason: (1) requires nonnegative demand, and Lemma 2's proof uses nonnegative revenue (p.3555)
--   - encoding: prices p ∈ [p̲, p̄] with demand f(p) and noise law Q(p) → demand rates λ ∈ [d̲, d̄] with price g(λ) = f⁻¹(λ) and noise law Q(λ) := Q(f⁻¹(λ)); |f(p) − f(p′)| = |λ − λ′| in A5; reason: the paper's own parametrization in (5); f is a bijection [p̲, p̄] → [d̲, d̄], so the instances are the same
--   - encoding: A1: f strictly decreasing on [p̲, p̄] with values in ℝ₊, prices in 𝒫 ⊂ ℝ₊, p̄ ≤ +∞ → 0 ≤ d̲ < d̄, g ≥ 0 on [d̲, d̄], g strictly decreasing on (d̲, d̄]; reason: with p̄ = +∞ the price at d̲ is not a real number; when d̲ > 0 the value g(d̲) is pinned by the continuity of r at d̲, and when d̲ = 0 it enters only through r(0) = 0; A4, A5 and demand ≥ 0 are also required of Q(d̲), which excludes no model (when p̄ = +∞, Q(p) converges in 𝒲₂ as p → ∞ by A5, and the limit satisfies them)
--   - encoding: r′, r″, r‴ exist on [d̲, d̄] (A2, A3) → r, r′, r″ differentiable within [d̲, d̄]; r′, r″, r‴ are iteratedDerivWithin on [d̲, d̄] (one-sided at the endpoints); reason: the derivatives of a function defined on a closed interval
--   - encoding: 𝒲₂(Q, Q′) = inf_Ξ √(𝔼|ξ − ξ′|²) → WassersteinDRO.StrongDuality.wasserstein 2 = (inf over couplings of ∫|ξ − ξ′|²)^{1/2} in ℝ≥0∞, compared with ofReal(L|λ − λ′|); reason: the square root is increasing and continuous, so it commutes with the infimum; same values
--   - encoding: λᵘ := argmax_{λ≥0} r(λ), rᵘ := max_{λ≥0} r(λ) (p.3541) → λᵘ is a datum of the model with IsMaxOn r [d̲, d̄] λᵘ and λᵘ ∈ (d̲, d̄); rᵘ = r(λᵘ); reason: r is defined only on [d̲, d̄] (Table 1, p.3542, writes argmax over [d̲, d̄]); the maximizer is unique by strict concavity
--   - generalization: the random quantities x_T − Δ̄→τ − ξ̄*→τ + ℓ̄*→τ + Δ_τ and x_T − ξ̄ʳ→τ for τ ≥ T♯ → arbitrary reals Δ̄, Ξ*, Ξʳ, ℓ̄ ≥ 0, Δ; reason: the chain is deterministic once (6) and (9) are substituted; the paper's quantities are particular values
--   - encoding: r evaluated at x_T − Δ̄→τ − ξ̄*→τ + ℓ̄*→τ + Δ_τ, x_T − Δ̄→τ − ξ̄*→τ + Δ_τ and x_T − ξ̄ʳ→τ → these points are assumed to lie in [d̲, d̄]; reason: r = λ f⁻¹(λ) is defined only on [d̲, d̄]; the chain is meaningful exactly there
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.2, Eq. (13), p.3544 (PDF p.8)

import Mathlib
import Definitions.Def_ResolvingPricing_Model

open MeasureTheory

namespace ResolvingPricing

/-- **Eq. (13)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3544: the Taylor and strict-concavity bound
r(x*_τ + Δ_τ) − r(xʳ_τ) = r(x_T − Δ̄→τ − ξ̄*→τ + ℓ̄*→τ + Δ_τ) − r(x_T − ξ̄ʳ→τ)
≤ r′(d̲)ℓ̄*→τ + r′(x_T)[Δ_τ − Δ̄→τ + ξ̄^δ→τ] − r″(x_T)ξ̄ʳ→τ[Δ_τ − Δ̄→τ + ξ̄^δ→τ]
  + (M/2)|ξ̄ʳ→τ|²|Δ_τ − Δ̄→τ + ξ̄^δ→τ| − (m/2)|Δ_τ − Δ̄→τ + ξ̄^δ→τ|²,
with `ξ̄^δ→τ = ξ̄ʳ→τ − ξ̄*→τ`.

Stated for real numbers `Δ̄ = Δ̄→τ`, `Ξ* = ξ̄*→τ`, `Ξʳ = ξ̄ʳ→τ`, `ℓ̄ = ℓ̄*→τ ≥ 0`, `Δ = Δ_τ`.

**Formalization Note.** The chain is deterministic once (6) and (9) are substituted. `r` is defined
on `[d̲, d̄]` only, so the points at which the chain evaluates `r` are assumed to lie there
(`x_T − Δ̄ − Ξ* + ℓ̄ + Δ`, `x_T − Δ̄ − Ξ* + Δ` and `x_T − Ξʳ`; `x_T` lies there by `hx`). `r′(d̲)` is the
right derivative. -/
theorem eq_13 (P : Model) (hP : P.Assumptions) (x : ℝ) (hx : x ∈ Set.Ioo P.dlo P.lamU)
    (Db Xs Xr lb Dl : ℝ) (hlb : 0 ≤ lb) (h₁ : x - Db - Xs + lb + Dl ∈ P.D)
    (h₂ : x - Db - Xs + Dl ∈ P.D) (h₃ : x - Xr ∈ P.D) :
    P.r (x - Db - Xs + lb + Dl) - P.r (x - Xr) ≤
      P.r1 P.dlo * lb + P.r1 x * (Dl - Db + (Xr - Xs)) - P.r2 x * Xr * (Dl - Db + (Xr - Xs))
        + P.M / 2 * |Xr| ^ 2 * |Dl - Db + (Xr - Xs)| - P.m / 2 * |Dl - Db + (Xr - Xs)| ^ 2 := by sorry

end ResolvingPricing
