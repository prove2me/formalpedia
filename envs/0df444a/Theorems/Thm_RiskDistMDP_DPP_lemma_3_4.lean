-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_3_4
-- name    : RiskDistMDP.DPP.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:47.666792+00:00
-- url     : https://prove2.me/theorems/15bcb0ed-205c-4cb2-9e3d-0adac3c4571e
-- title:
--   Lemma 3.4 (corrected: Def. 2.3 (iii) weights) — lower semicontinuity of $(x,\lambda)\mapsto G^\lambda_tv(x)$
-- statement:
--   Let $x_n\to x_0$ in $\mathbb X$ and $\lambda_n\to\lambda_0$ weakly in $\Lambda$. Under Assumption 2.13 (i), (iii), (iv), if $v\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$ is lower semicontinuous, then
--   $$\liminf_{n\to\infty}G^{\lambda_n}_tv(x_n)\ge G^{\lambda_0}_tv(x_0).$$
--
--   Lower semicontinuity is what lets the Bellman operator preserve lower semicontinuous value functions and attain its infimum.
--
--   Differences from the source:
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 3.4, p. 16

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_G
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 3.4** (arXiv:2203.09612v4, p.16). Let `x_n → x₀` in `𝕏` and `λ_n → λ₀` in `Λ`. Under
Assumption 2.13 (i), (iii), (iv), if `v ∈ ℓ^∞(𝕏, ℬ(𝕏))` is lower semicontinuous, then
`liminf_{n→∞} G^{λ_n}_t v(x_n) ≥ G^{λ₀}_t v(x₀)`. -/
theorem lemma_3_4 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hi : A213i R.toBorelMDP)
    (hiii : A213iii R.σ) (hiv : A213iv R.toBorelMDP b)
    (t : ℕ) (ht : 1 ≤ t) (v : 𝕏 → ℝ) (hv : IsLinf v) (hlsc : LowerSemicontinuous v)
    (xs : ℕ → 𝕏) (x0 : 𝕏) (ls : ℕ → ProbabilityMeasure 𝔸) (l0 : ProbabilityMeasure 𝔸)
    (hx : Tendsto xs atTop (𝓝 x0)) (hl : Tendsto ls atTop (𝓝 l0)) :
    G R t l0 v x0 ≤ liminf (fun n => G R t (ls n) v (xs n)) atTop := by sorry

end RiskDistMDP.DPP
