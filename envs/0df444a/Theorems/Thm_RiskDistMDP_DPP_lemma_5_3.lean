-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_5_3
-- name    : RiskDistMDP.DPP.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:08.564799+00:00
-- url     : https://prove2.me/theorems/cf60a5b5-4fb9-4fca-9951-9aaabf8355b8
-- title:
--   Lemma 5.3 (corrected: $J^*_{0,\infty}\le\sigma_0(\delta_0)+\gamma b/(1-\gamma)$; one cost bound $b$; Def. 2.3 (iii) weights) — convergence and bounds of optimal values
-- statement:
--   Suppose $\gamma\in[0,1)$ and $(\sigma_{t,x})$ is normalized. Under Assumption 2.13 with one cost bound $b$, for every $t\in\mathbb N$, $(J^*_{t,T})_{T}$ converges uniformly on $\mathbb X$ and
--   $$\sup_{t\in\mathbb N}\|J^*_{t,\infty}\|_\infty\le\frac{b}{1-\gamma}.$$
--   Moreover $(J^*_{0,T})_T$ converges and
--   $$J^*_{0,\infty}\le\sigma_0(\delta_0)+\frac{\gamma b}{1-\gamma}.$$
--
--   Differences from the source:
--   - correction: J*_{0,∞} ≤ γb/(1−γ) → J*_{0,∞} ≤ σ₀(δ₀) + γb/(1−γ); reason: σ₀ is outside "normalized" and Assumption 2.6: with σ₀ = mean + K, K > 2γb/(1−γ), J*_{0,∞} ≥ K − γb/(1−γ) > γb/(1−γ); the corrected bound is the printed one when σ₀(δ₀) = 0
--   - correction: Assumption 2.13 (iv): for any t, ‖C_t‖_∞ ≤ b for some b > 0 (b may depend on t) → one constant b for all t (A213iv with fun _ => b); reason: with a t-dependent bound the infinite-horizon results fail (𝕏, 𝔸 singletons, γ = 1/2, C_t ≡ 4^t, σ the mean: J*_{t,T} diverges); §5 bounds the values by b/(1−γ), one constant
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: lim_{T→∞} in (2.13), (5.1), (5.4) → limUnder atTop, pointwise, in ℝ for t ≥ 1 and in EReal at time 0; reason: the limits exist under the hypotheses (Lemmas 2.9, 5.1, 5.3), so limUnder is the limit
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 5.3, p. 22

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_JstarInf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 5.3** (arXiv:2203.09612v4, p.22; corrected: the time-0 bound carries `σ₀(δ₀)`). Suppose
`γ ∈ [0,1)` and `(σ_{t,x})` is normalized. Under Assumption 2.13, for every `t ∈ ℕ`,
`(J*_{t,T})_{T>t}` converges uniformly and `sup_{t∈ℕ} ‖J*_{t,∞}‖_∞ ≤ b/(1−γ)`. Moreover
`(J*_{0,T})_{T∈ℕ}` converges and `J*_{0,∞} ≤ σ₀(δ₀) + γb/(1−γ)`.

**Formalization Note** The page prints `J*_{0,∞} ≤ γb/(1−γ)`, which needs `σ₀` normalized, and `σ₀`
is outside "normalized" (p.9) and outside Assumption 2.6: with `σ₀ = mean + K`,
`K > 2γb/(1−γ)`, `J*_{0,∞} ≥ K − γb/(1−γ) > γb/(1−γ)`. The corrected bound is the printed one when
`σ₀(δ₀) = 0`. `b` is one constant for all `t`. The time-0 convergence is in `EReal`. -/
theorem lemma_5_3 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (hγ : R.γ < 1) (hnorm : R.Normalized) (b : ℝ)
    (hA : Assumption213 R (fun _ => b)) :
    (∀ t, 1 ≤ t → TendstoUniformly (fun T x => Jstar R T t x) (JstarInf R t) atTop) ∧
    (∀ t, 1 ≤ t → ∀ x, |JstarInf R t x| ≤ b / (1 - R.γ)) ∧
    (∃ l : EReal, Tendsto (fun T => Jstar0 R T) atTop (𝓝 l)) ∧
    Jstar0Inf R ≤ R.σ0 (Measure.dirac 0) + ((R.γ * b / (1 - R.γ) : ℝ) : EReal) := by sorry

end RiskDistMDP.DPP
