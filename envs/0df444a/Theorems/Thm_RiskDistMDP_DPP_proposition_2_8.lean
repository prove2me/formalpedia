-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_proposition_2_8
-- name    : RiskDistMDP.DPP.proposition_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:54.768836+00:00
-- url     : https://prove2.me/theorems/ae3508c2-fad6-47bf-b0f4-d8bbcd63d30d
-- title:
--   Proposition 2.8 (corrected: Def. 2.3 (iii) weights) — time consistency of the finite-horizon DRM
-- statement:
--   Let $0\le s\le t<T$, and let $\mathfrak Z,\mathfrak Z'$ be bounded random variables. If $\mathbb P(Z_r=Z'_r)=1$ for $r=s,\dots,t$ and
--   $$\mathbb P\big(\varsigma^{\mathfrak X,\gamma}_{t+1,x,T}(\mathfrak Z)\le\varsigma^{\mathfrak X,\gamma}_{t+1,x,T}(\mathfrak Z'),\ x\in\mathbb X\big)=1,$$
--   then $\mathbb P\big(\varsigma^{\mathfrak X,\gamma}_{s,x,T}(\mathfrak Z)\le\varsigma^{\mathfrak X,\gamma}_{s,x,T}(\mathfrak Z'),\ x\in\mathbb X\big)=1$ when $s\ge1$, and $\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak Z)\le\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak Z')$ when $s=0$.
--
--   Time consistency: if two cost streams agree up to time $t$ and one is riskier from $t+1$ on, it is riskier at every earlier time.
--
--   Differences from the source:
--   - reading: ℙ(ς_{s,x,T}(ℨ) ≤ ς_{s,x,T}(ℨ′), x ∈ 𝕏) = 1 at s = 0 → ς_{0,T}(ℨ) ≤ ς_{0,T}(ℨ′); reason: the time-0 DRM has no x and is a number (p.9)
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: ℨ ⊂ L^∞(Ω, ℋ, ℙ) and ‖Z_r‖_∞ → Z_r measurable with |Z_r| ≤ c_r a.s., bounds stated for every such c; reason: equivalent: take c_r = ‖Z_r‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Proposition 2.8, p. 10

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsInfoSetting
import Definitions.Def_RiskDistMDP_DPP_Assumption26
import Definitions.Def_RiskDistMDP_DPP_drm

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Proposition 2.8** (arXiv:2203.09612v4, p.10; time consistency of the finite-horizon DRM). Let
`0 ≤ s ≤ t < T` and `ℨ, ℨ′ ⊂ L^∞(Ω, ℋ, ℙ)`. If `ℙ(Z_r = Z′_r) = 1` for `r = s, …, t` and
`ℙ(ς_{t+1,x,T}(ℨ) ≤ ς_{t+1,x,T}(ℨ′), x ∈ 𝕏) = 1`, then `ℙ(ς_{s,x,T}(ℨ) ≤ ς_{s,x,T}(ℨ′), x ∈ 𝕏) = 1`.

**Formalization Note** "`ℙ(…, x ∈ 𝕏) = 1`" is `∀ᵐ ω, ∀ x, …`. For `s = 0` the DRM has no `x`
(it is `ς_{0,T}`, a number), so the conclusion is `ς_{0,T}(ℨ) ≤ ς_{0,T}(ℨ′)` (reading R8). -/
theorem proposition_2_8 {𝕏 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (σ0 : Measure ℝ → EReal) (σ : ℕ → 𝕏 → Measure ℝ → EReal) (hσ : IsRiskFamily σ0 σ)
    (h26 : Assumption26 σ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔛 : ℕ → Ω → 𝕏) (h𝔛 : ∀ t, 1 ≤ t → Measurable[ℱ t] (𝔛 t))
    (Z Z' : ℕ → Ω → ℝ) (hZ : ∀ t, Measurable (Z t)) (hZ' : ∀ t, Measurable (Z' t))
    (hZb : ∀ t, ∃ c : ℝ, ∀ᵐ ω ∂Pr, |Z t ω| ≤ c) (hZb' : ∀ t, ∃ c : ℝ, ∀ᵐ ω ∂Pr, |Z' t ω| ≤ c)
    (s t T : ℕ) (hst : s ≤ t) (htT : t < T)
    (heq : ∀ r, s ≤ r → r ≤ t → Z r =ᵐ[Pr] Z' r)
    (hnext : ∀ᵐ ω ∂Pr, ∀ x, drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T (t + 1) x ω ≤ drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z' T (t + 1) x ω) :
    (1 ≤ s → ∀ᵐ ω ∂Pr, ∀ x, drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T s x ω ≤ drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z' T s x ω) ∧
    (s = 0 → drm0 σ0 σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T ≤ drm0 σ0 σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z' T) := by sorry

end RiskDistMDP.DPP
