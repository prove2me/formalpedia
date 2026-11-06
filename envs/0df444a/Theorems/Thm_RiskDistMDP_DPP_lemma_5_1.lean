-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_5_1
-- name    : RiskDistMDP.DPP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:58.34582+00:00
-- url     : https://prove2.me/theorems/a19185fc-c9cf-4f1d-bd5c-e3efeaad3388
-- title:
--   Lemma 5.1 (corrected: one cost bound $b$; Def. 2.3 (iii) weights) — convergence and recursion of policy values
-- statement:
--   Suppose $\gamma\in[0,1)$ and $(\sigma_{t,x})$ is normalized, and $C_t$ is lower semicontinuous with $\|C_t\|_\infty\le b$ for all $t$ (Assumption 2.13 (iv)). For every $\mathfrak p\in\Pi$, $(J^{\mathfrak p}_{0,T})_T$ converges, $(J^{\mathfrak p}_{t,T})_T$ converges uniformly on $\mathbb X$ for every $t\in\mathbb N$, and
--   $$J^{\mathfrak p}_{t,\infty}=H^{\mathfrak p}_tJ^{\mathfrak p}_{t+1,\infty}\ (t\in\mathbb N),\qquad J^{\mathfrak p}_{0,\infty}=H_0J^{\mathfrak p}_{1,\infty},\qquad \sup_{t\in\mathbb N}\|J^{\mathfrak p}_{t,\infty}\|_\infty\le\frac{b}{1-\gamma}.\tag{5.3}$$
--
--   This identifies the infinite-horizon value of a Markovian policy with a solution of its policy equation.
--
--   Differences from the source:
--   - correction: Assumption 2.13 (iv): for any t, ‖C_t‖_∞ ≤ b for some b > 0 (b may depend on t) → one constant b for all t (A213iv with fun _ => b); reason: with a t-dependent bound the infinite-horizon results fail (𝕏, 𝔸 singletons, γ = 1/2, C_t ≡ 4^t, σ the mean: J*_{t,T} diverges); §5 bounds the values by b/(1−γ), one constant
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: lim_{T→∞} in (2.13), (5.1), (5.4) → limUnder atTop, pointwise, in ℝ for t ≥ 1 and in EReal at time 0; reason: the limits exist under the hypotheses (Lemmas 2.9, 5.1, 5.3), so limUnder is the limit
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 5.1, p. 21

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies
import Definitions.Def_RiskDistMDP_DPP_JpolInf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 5.1** (arXiv:2203.09612v4, p.21). Suppose `γ ∈ [0,1)` and `(σ_{t,x})` is normalized. Under
Assumption 2.13 (iv), for every `𝔭 ∈ Π`, `(J^𝔭_{0,T})_{T∈ℕ}` converges and `(J^𝔭_{t,T})_{T}` converges
uniformly for `t ∈ ℕ`. Moreover `J^𝔭_{t,∞} = H^𝔭_t J^𝔭_{t+1,∞}` for `t ∈ ℕ` and
`J^𝔭_{0,∞} = H₀ J^𝔭_{1,∞}` (5.3), and `sup_{t∈ℕ} ‖J^𝔭_{t,∞}‖_∞ ≤ b/(1−γ)`.

**Formalization Note** `b` is one constant for all `t` (the page's `b/(1−γ)` presupposes it). The
time-0 convergence is in `EReal`. -/
theorem lemma_5_1 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (hγ : R.γ < 1) (hnorm : R.Normalized) (b : ℝ)
    (hiv : A213iv R.toBorelMDP (fun _ => b))
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (h𝔭 : 𝔭 ∈ MarkovPolicies R.toBorelMDP) :
    (∃ l : EReal, Tendsto (fun T => Jpol0 R 𝔭 T) atTop (𝓝 l)) ∧
    (∀ t, 1 ≤ t → TendstoUniformly (fun T x => Jpol R 𝔭 T t x) (JpolInf R 𝔭 t) atTop) ∧
    (∀ t, 1 ≤ t → ∀ x, ((JpolInf R 𝔭 t x : ℝ) : EReal) = H R 𝔭 t (JpolInf R 𝔭 (t + 1)) x) ∧
    Jpol0Inf R 𝔭 = H0 R (JpolInf R 𝔭 1) ∧
    (∀ t, 1 ≤ t → ∀ x, |JpolInf R 𝔭 t x| ≤ b / (1 - R.γ)) := by sorry

end RiskDistMDP.DPP
