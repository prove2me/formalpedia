-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_3_2
-- name    : RiskDistMDP.DPP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:42.786835+00:00
-- url     : https://prove2.me/theorems/d9f19db8-5400-46e4-9661-291d4dc053ef
-- title:
--   Lemma 3.2 (corrected: Def. 2.3 (iii) weights) — measurability of $(x,\lambda)\mapsto G^\lambda_tv(x)$ and of $H^{\mathfrak p}_tv$
-- statement:
--   Under Assumption 2.13 (i), (iii), (iv), for every $t\in\mathbb N$ and $v\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$, the map
--   $$(x,\lambda)\mapsto G^\lambda_tv(x)$$
--   is $\mathcal B(\mathbb X)\otimes\mathcal E(\Lambda)$-measurable, and consequently $x\mapsto H^{\mathfrak p}_tv(x)$ is Borel for every $\mathfrak p\in\Pi$.
--
--   This shows that $G^\lambda_t$ and $H^{\mathfrak p}_t$ map $\ell^\infty$ into $\ell^\infty$.
--
--   Differences from the source:
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 3.2, p. 15

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_H
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 3.2** (arXiv:2203.09612v4, p.15). Under Assumption 2.13 (i), (iii), (iv), for every
`v ∈ ℓ^∞(𝕏, ℬ(𝕏))` the map `(x, λ) ↦ G^λ_t v(x)` is `ℬ(𝕏) ⊗ ℰ(Λ)`-measurable; consequently
`x ↦ H^𝔭_t v(x)` is `ℬ(𝕏)`-measurable for every `𝔭 ∈ Π`.

**Formalization Note** `ℰ(Λ)` is Mathlib's (Giry) σ-algebra on `ProbabilityMeasure 𝔸`. The maps
are `EReal`-valued; their values are finite by Lemma 3.1, so measurability into `EReal` is
measurability into `ℝ`. -/
theorem lemma_3_2 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hi : A213i R.toBorelMDP)
    (hiii : A213iii R.σ) (hiv : A213iv R.toBorelMDP b)
    (t : ℕ) (ht : 1 ≤ t) (v : 𝕏 → ℝ) (hv : IsLinf v) :
    Measurable (fun p : 𝕏 × ProbabilityMeasure 𝔸 => G R t p.2 v p.1) ∧
    ∀ 𝔭 ∈ MarkovPolicies R.toBorelMDP, Measurable (fun x => H R 𝔭 t v x) := by sorry

end RiskDistMDP.DPP
