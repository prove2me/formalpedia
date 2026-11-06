-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_proposition_4_3
-- name    : RiskDistMDP.DPP.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:50.394196+00:00
-- url     : https://prove2.me/theorems/9c32a8de-2ea5-40da-a9f8-bdfb9a21fdd5
-- title:
--   Proposition 4.3 (corrected: Def. 2.3 (iii) weights) — finite horizon: Markovian pairs are no worse than any pair of $\Psi$
-- statement:
--   Let $\gamma\in[0,1]$ and $T\in\mathbb N$. Under Assumption 2.13, for every $(\mathfrak X,\mathfrak A)\in\Psi$,
--   $$\inf_{(\mathfrak X^{\mathfrak p},\mathfrak A^{\mathfrak p})\in\Psi}\varsigma^{\mathfrak X^{\mathfrak p}}_{0,T}(\mathfrak C^{\mathfrak p})\le\varsigma^{\mathfrak X}_{0,T}(\mathfrak C),$$
--   where the infimum runs over the pairs of $\Psi$ associated with some $\mathfrak p\in\Pi$.
--
--   No history-dependent or randomized pair in $\Psi$ beats the best Markovian one.
--
--   Differences from the source:
--   - reading: (𝔛^𝔭, 𝔄^𝔭) associated with 𝔭 via (2.5), ℙ(A_t ∈ B | σ(X_t)) = π_t(X_t)(B) → MarkovAssoc: ℙ(A_t ∈ B | 𝒰_t) = π_t(X_t)(B) a.s., i.e. (2.4) and (2.5) together; reason: §2.2 derives (2.5) from the Markovian property (2.4); with (2.5) alone Lemma 3.3 fails (X a singleton, A_t = A₁ a fair coin, 𝒢_t = σ(A₁), σ₂ = ess sup, T = 2: ς_{1,x,2} = 1/2 but H₁∘H₂O = 1)
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: (2.2) ℙ(X_{t+1} ∈ B | 𝒢_t) = ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) and (2.3) ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) = P(t, X_t, A_t, B) → one equation ℙ(X_{t+1} ∈ B | 𝒢_t) = P(t, X_t, A_t, B) a.s. (InPsiClass); reason: equivalent: the right side is σ(X_t) ∨ σ(A_t)-measurable and σ(X_t) ∨ σ(A_t) ⊆ 𝒢_t, so the tower property gives (2.2) and (2.3) back
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Proposition 4.3, p. 19

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_Assumption211
import Definitions.Def_RiskDistMDP_DPP_cost
import Definitions.Def_RiskDistMDP_DPP_drm

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Proposition 4.3** (arXiv:2203.09612v4, p.19). Let `γ ∈ [0,1]` and `T ∈ ℕ`. Under Assumption 2.13,
`inf_{(𝔛^𝔭,𝔄^𝔭)∈Ψ} ς^{𝔛^𝔭}_{0,T}(ℭ^𝔭) ≤ ς^𝔛_{0,T}(ℭ)` for every `(𝔛, 𝔄) ∈ Ψ`: no history-dependent
pair of `Ψ` does better than the Markovian ones.

**Formalization Note** The infimum runs in `EReal` over the pairs of `Ψ` associated with some
`𝔭 ∈ Π` (`markovPairs`, association in the sense R1). -/
theorem proposition_4_3 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hA : Assumption213 R b) (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) (hΨ : Assumption211 R.toBorelMDP Pr ℱ 𝒢 Ψ)
    (T : ℕ) (hT : 1 ≤ T) (q : (ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) (hq : q ∈ Ψ) :
    (⨅ q' ∈ markovPairs R.toBorelMDP Pr ℱ 𝒢 Ψ, drm0 R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q'.1 (cost R.toBorelMDP q') T) ≤ drm0 R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q) T := by sorry

end RiskDistMDP.DPP
