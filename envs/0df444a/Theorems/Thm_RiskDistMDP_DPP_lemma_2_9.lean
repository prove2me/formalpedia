-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_2_9
-- name    : RiskDistMDP.DPP.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:44.031189+00:00
-- url     : https://prove2.me/theorems/c3df1a35-7a76-4da3-834e-433ea9883657
-- title:
--   Lemma 2.9 (corrected: finiteness of $\varsigma_{0,\infty}$ needs $\sigma_0(\delta_0)\ne+\infty$; Def. 2.3 (iii) weights) — the infinite-horizon DRM is well defined
-- statement:
--   Suppose $\sup_t\|Z_t\|_\infty<\infty$, $\gamma\in[0,1)$ and $(\sigma_{t,x})$ is normalized. For every $t\in\mathbb N$:
--
--   1. for a.e. $\omega$, $(\varsigma^{\mathfrak X,\gamma}_{t,x,T}(\mathfrak Z)(\omega))_{T}$ converges for every $x\in\mathbb X$;
--   2. if $|Z_r|\le c$ a.s. for all $r$, then a.s. for every $x$
--   $$|\varsigma^{\mathfrak X,\gamma}_{t,x,\infty}(\mathfrak Z)|\le\frac{c}{1-\gamma};$$
--   3. there is a $\mathcal B(\mathbb X)\otimes\mathcal U_t$-measurable real $\bar\varsigma_{t,x,\infty}(\mathfrak Z)$ equal to $\varsigma_{t,x,\infty}(\mathfrak Z)$ for every $x$, a.s.
--
--   Moreover $\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak Z)$ converges as $T\to\infty$, and $\varsigma^{\mathfrak X,\gamma}_{0,\infty}(\mathfrak Z)$ is finite when $\sigma_0(\delta_0)\ne+\infty$.
--
--   This justifies the limits (2.13) defining the infinite-horizon objective.
--
--   Differences from the source:
--   - correction: ς^{𝔛,γ}_{0,∞}(ℨ) is finite → finite under the added hypothesis σ₀(δ₀) ≠ +∞, on that clause only; reason: σ₀ ≡ +∞ on 𝒫_b(ℝ) satisfies Definition 2.3 and every assumption (Assumption 2.6 and normalization do not cover σ₀), and then ς_{0,∞} = +∞
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - encoding: Assumption 2.6 (measurability and bounds b_t) standing → only its measurability half is a hypothesis; reason: under normalization the bounds hold with b_t = 0, so the other half excludes nothing
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: ℨ ⊂ L^∞(Ω, ℋ, ℙ) and ‖Z_r‖_∞ → Z_r measurable with |Z_r| ≤ c_r a.s., bounds stated for every such c; reason: equivalent: take c_r = ‖Z_r‖_∞
--   - encoding: lim_{T→∞} in (2.13), (5.1), (5.4) → limUnder atTop, pointwise, in ℝ for t ≥ 1 and in EReal at time 0; reason: the limits exist under the hypotheses (Lemmas 2.9, 5.1, 5.3), so limUnder is the limit
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 2.9, p. 10

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsInfoSetting
import Definitions.Def_RiskDistMDP_DPP_Assumption26
import Definitions.Def_RiskDistMDP_DPP_drmInf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 2.9** (arXiv:2203.09612v4, p.10; corrected: the last clause needs `σ₀(δ₀) ≠ +∞`). Suppose
`sup_{t∈ℕ₀} ‖Z_t‖_∞ < ∞`, `γ ∈ [0,1)` and `(σ_{t,x})` is normalized. For every `t ∈ ℕ`:
`ℙ((ς_{t,x,T}(ℨ))_{T∈ℕ} converges for every x) = 1`; `ℙ(|ς_{t,x,∞}(ℨ)| ≤ (1−γ)^{−1}‖ℨ‖_∞, x ∈ 𝕏) = 1`;
and there is a `ℬ(𝕏) ⊗ 𝒰_t`-measurable `ς̄_{t,x,∞}(ℨ)` with `ℙ(ς_{t,x,∞}(ℨ) = ς̄_{t,x,∞}(ℨ), x ∈ 𝕏) = 1`.
Finally `ς_{0,T}(ℨ)` converges as `T → ∞`, and `ς_{0,∞}(ℨ)` is finite when `σ₀(δ₀) ≠ +∞`.

**Formalization Note** `‖ℨ‖_∞ = sup_t ‖Z_t‖_∞` enters through any `c` with `|Z_r| ≤ c` a.s. for all
`r`. The printed "ς_{0,∞}(ℨ) is finite" fails for `σ₀ ≡ +∞` on `𝒫_b(ℝ)`, which satisfies Definition 2.3
and every assumption of the paper (Assumption 2.6 and normalization do not cover `σ₀`); the
finiteness clause is therefore stated under `σ₀(δ₀) ≠ +∞`. Convergence at `t = 0` holds in `EReal`
without it. The `b_t` of Assumption 2.6 are `0` under normalization, so only the measurability half of
Assumption 2.6 is a hypothesis. -/
theorem lemma_2_9 {𝕏 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (σ0 : Measure ℝ → EReal) (σ : ℕ → 𝕏 → Measure ℝ → EReal) (hσ : IsRiskFamily σ0 σ)
    (hmeas : SigmaMeasurable σ) (hnorm : FamilyNormalized σ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (𝔛 : ℕ → Ω → 𝕏) (h𝔛 : ∀ t, 1 ≤ t → Measurable[ℱ t] (𝔛 t))
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t, Measurable (Z t)) (hsup : ∃ c : ℝ, ∀ t, ∀ᵐ ω ∂Pr, |Z t ω| ≤ c) :
    (∀ t, 1 ≤ t →
      (∀ᵐ ω ∂Pr, ∀ x, ∃ l : EReal, Tendsto (fun T => drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T t x ω) atTop (𝓝 l)) ∧
      (∀ c : ℝ, (∀ r, ∀ᵐ ω ∂Pr, |Z r ω| ≤ c) → ∀ᵐ ω ∂Pr, ∀ x,
        ((-(c / (1 - γ)) : ℝ) : EReal) ≤ drmInf σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z t x ω ∧
          drmInf σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z t x ω ≤ ((c / (1 - γ) : ℝ) : EReal)) ∧
      (∃ ςbar : 𝕏 → Ω → ℝ,
        Measurable[@Prod.instMeasurableSpace 𝕏 Ω _ (decInfo ℱ 𝒢 t)] (fun p : 𝕏 × Ω => ςbar p.1 p.2) ∧
        ∀ᵐ ω ∂Pr, ∀ x, drmInf σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z t x ω = ((ςbar x ω : ℝ) : EReal))) ∧
    (∃ l : EReal, Tendsto (fun T => drm0 σ0 σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T) atTop (𝓝 l)) ∧
    (σ0 (Measure.dirac 0) ≠ ⊤ →
      drm0Inf σ0 σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z ≠ ⊤ ∧ drm0Inf σ0 σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z ≠ ⊥) := by sorry

end RiskDistMDP.DPP
