-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_3_5
-- name    : RiskDistMDP.DPP.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:55.118784+00:00
-- url     : https://prove2.me/theorems/075aab2f-134f-4db5-88fa-5778fd4f7a17
-- title:
--   Lemma 3.5 (corrected: Def. 2.3 (iii) weights) — $G^\lambda_t$ and $H_0$ are $\gamma$-Lipschitz in sup norm
-- statement:
--   Under Assumption 2.13 (iv), for $t\in\mathbb N$, $\lambda\in\Lambda$ and $v_1,v_2\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$ with $|v_1-v_2|\le c$,
--   $$\|G^\lambda_tv_1-G^\lambda_tv_2\|_\infty\le\gamma c\qquad\text{and}\qquad |H_0v_1-H_0v_2|\le\gamma c,$$
--   the second in the form $H_0v_1\le H_0v_2+\gamma c$ and $H_0v_2\le H_0v_1+\gamma c$.
--
--   This is the contraction estimate behind the infinite-horizon results.
--
--   Differences from the source:
--   - encoding: |H₀v₁ − H₀v₂| ≤ γ‖v₁ − v₂‖_∞ (and the same with ‖·‖_∞ for G) → two one-sided inequalities in EReal; reason: equal to the printed bound when the values are finite; H₀ may be +∞ (σ₀ is outside Assumption 2.6), where the difference is undefined
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 3.5, p. 17

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_G
import Definitions.Def_RiskDistMDP_DPP_H0
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 3.5** (arXiv:2203.09612v4, p.17). Under Assumption 2.13 (iv), for every `t ∈ ℕ`, `λ ∈ Λ` and
`v₁, v₂ ∈ ℓ^∞(𝕏, ℬ(𝕏))`, `‖G^λ_t v₁ − G^λ_t v₂‖_∞ ≤ γ‖v₁ − v₂‖_∞` and
`|H₀ v₁ − H₀ v₂| ≤ γ‖v₁ − v₂‖_∞`.

**Formalization Note** `‖v₁ − v₂‖_∞` enters through any `c` with `|v₁ − v₂| ≤ c`. Both bounds are
written as two one-sided inequalities in `EReal`. For `G` (finite-valued, Lemma 3.1) this is the
absolute-value bound. For `H₀`, which may be `+∞` (`σ₀` is not covered by Assumption 2.6), the
one-sided form is the meaningful one and equals the printed bound whenever `H₀` is finite. -/
theorem lemma_3_5 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hiv : A213iv R.toBorelMDP b)
    (t : ℕ) (ht : 1 ≤ t) (l : ProbabilityMeasure 𝔸) (v₁ v₂ : 𝕏 → ℝ) (hv₁ : IsLinf v₁)
    (hv₂ : IsLinf v₂) (c : ℝ) (hc : ∀ y, |v₁ y - v₂ y| ≤ c) :
    (∀ x, G R t l v₁ x ≤ G R t l v₂ x + ((R.γ * c : ℝ) : EReal) ∧
      G R t l v₂ x ≤ G R t l v₁ x + ((R.γ * c : ℝ) : EReal)) ∧
    (H0 R v₁ ≤ H0 R v₂ + ((R.γ * c : ℝ) : EReal) ∧
      H0 R v₂ ≤ H0 R v₁ + ((R.γ * c : ℝ) : EReal)) := by sorry

end RiskDistMDP.DPP
