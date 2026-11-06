-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_2_7
-- name    : RiskDistMDP.DPP.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:50.328983+00:00
-- url     : https://prove2.me/theorems/ccb40555-3c78-4b74-8513-5aeb767c827f
-- title:
--   Lemma 2.7 (corrected: $b_r$ in the sum; Def. 2.3 (iii) weights) — measurability and bound of the finite-horizon DRM
-- statement:
--   Let $\gamma\in[0,1]$, let $\mathfrak X$ be $\mathbb F$-adapted, let $(\sigma_{t,x})$ satisfy Definition 2.3 and Assumption 2.6 with constants $b_t$, and let $\mathfrak Z=(Z_t)$ be bounded random variables with $|Z_r|\le c_r$ a.s. For $t,T\in\mathbb N$ with $0<t<T$:
--
--   1. $(x,\omega)\mapsto\varsigma^{\mathfrak X,\gamma}_{t,x,T}(\mathfrak Z)(\omega)$ is $\mathcal B(\mathbb X)\otimes\mathcal U_t$-measurable;
--   2. for a.e. $\omega$ the values $\varsigma^{\mathfrak X,\gamma}_{t+1,x,T}(\mathfrak Z)(\omega)$ are finite for every $x$;
--   3. $$|W^T_t|\le\sum_{r=t}^T\gamma^{r-t}\,(b_r+c_r)\quad\text{a.s.};$$
--   4. if $(\sigma_{t,x})$ is normalized, $|W^T_t|\le\sum_{r=t}^T\gamma^{r-t}c_r$ a.s.
--
--   The lemma makes the recursion (2.9) well defined and bounds the DRM by the discounted cost bounds.
--
--   Differences from the source:
--   - correction: ‖W^T_t‖_∞ ≤ Σ_{r=t}^T γ^{r−t}(b_t + ‖Z_r‖_∞) → Σ_{r=t}^T γ^{r−t}(b_r + c_r); reason: with 𝕏 a singleton, T = t+1, Z ≡ 0, γ = 1, σ_{t,x} the mean (b_t = 0) and σ_{T,x} the mean plus 5 (b_T = 5), W^T_t = 5 while the printed bound is 0; (2.11) in the proof has b_T
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - generalization: (the values of ς_{t+1,x,T} are used as real numbers without comment) → an added conclusion: for a.e. ω they are finite for every x; reason: it makes W^T_t a real random variable; dropping the conjunct gives the source statement
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: ℨ ⊂ L^∞(Ω, ℋ, ℙ) and ‖Z_r‖_∞ → Z_r measurable with |Z_r| ≤ c_r a.s., bounds stated for every such c; reason: equivalent: take c_r = ‖Z_r‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 2.7, p. 9

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsInfoSetting
import Definitions.Def_RiskDistMDP_DPP_Assumption26
import Definitions.Def_RiskDistMDP_DPP_drm

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 2.7** (arXiv:2203.09612v4, p.9; corrected: `b_r` inside the sum). Let `ℨ = (Z_t)_{t∈ℕ₀}`
be bounded random variables and `t, T ∈ ℕ` with `0 < t < T`. Then `(x, ω) ↦ ς^{𝔛,γ}_{t,x,T}(ℨ)(ω)` is
`ℬ(𝕏) ⊗ 𝒰_t`-measurable and `‖W^T_t‖_∞ ≤ Σ_{r=t}^T γ^{r−t}(b_r + ‖Z_r‖_∞)`; if `(σ_{t,x})` is
normalized, `‖W^T_t‖_∞ ≤ Σ_{r=t}^T γ^{r−t}‖Z_r‖_∞`.

**Formalization Note** The page prints `b_t` inside the sum; with `𝕏` a singleton, `T = t+1`,
`Z ≡ 0`, `γ = 1`, `σ_{t,x}` the mean and `σ_{T,x}` the mean plus `5`, `W^T_t = 5` while the printed
bound is `0`. `‖Z_r‖_∞` enters through any `c r` with `|Z_r| ≤ c r` a.s. (taking `c r = ‖Z_r‖_∞` gives
the printed form). The second conjunct (the values `ς_{t+1,x,T}` are finite, so `W^T_t` is a real
random variable) is implicit on the page. -/
theorem lemma_2_7 {𝕏 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (σ : ℕ → 𝕏 → Measure ℝ → EReal) (hσ : ∀ t, 1 ≤ t → ∀ x, IsDistRiskMeasure (σ t x))
    (hmeas : SigmaMeasurable σ) (bσ : ℕ → ℝ) (hb : SigmaBounded σ bσ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔛 : ℕ → Ω → 𝕏) (h𝔛 : ∀ t, 1 ≤ t → Measurable[ℱ t] (𝔛 t))
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t, Measurable (Z t)) (c : ℕ → ℝ) (hc : ∀ t, ∀ᵐ ω ∂Pr, |Z t ω| ≤ c t)
    (t T : ℕ) (ht : 0 < t) (htT : t < T) :
    Measurable[@Prod.instMeasurableSpace 𝕏 Ω _ (decInfo ℱ 𝒢 t)]
        (fun p : 𝕏 × Ω => drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T t p.1 p.2) ∧
    (∀ᵐ ω ∂Pr, ∀ x, drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T (t + 1) x ω ≠ ⊤ ∧ drm σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T (t + 1) x ω ≠ ⊥) ∧
    (∀ᵐ ω ∂Pr, |drmW σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T t ω| ≤
      ∑ r ∈ Finset.Icc t T, γ ^ (r - t) * (bσ r + c r)) ∧
    (FamilyNormalized σ → ∀ᵐ ω ∂Pr, |drmW σ γ Pr (decInfo ℱ 𝒢) 𝔛 Z T t ω| ≤
      ∑ r ∈ Finset.Icc t T, γ ^ (r - t) * c r) := by sorry

end RiskDistMDP.DPP
