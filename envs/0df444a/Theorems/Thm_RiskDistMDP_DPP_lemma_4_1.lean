-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_4_1
-- name    : RiskDistMDP.DPP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:30.321249+00:00
-- url     : https://prove2.me/theorems/5ed3a39b-d2a8-4013-b37d-8db14fb15193
-- title:
--   Lemma 4.1 (corrected: Def. 2.3 (iii) weights) — lower semicontinuity of $J^*_{t,T}$
-- statement:
--   Under Assumption 2.13, for $t,T\in\mathbb N$ with $t\le T$, $x\mapsto J^*_{t,T}(x)$ is lower semicontinuous on $\mathbb X$.
--
--   In particular $J^*_{t,T}$ is Borel, so the recursion (4.4) stays inside $\ell^\infty$.
--
--   Differences from the source:
--   - generalization: t < T → 1 ≤ t ≤ T; reason: the proof starts at t = T (J*_{T,T} = S_T O); the source statement is the case t < T
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 4.1, p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_Jstar

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 4.1** (arXiv:2203.09612v4, p.18). Under Assumption 2.13, for `t, T ∈ ℕ` with `t ≤ T`,
`x ↦ J*_{t,T}(x)` is lower semicontinuous on `𝕏`.

**Formalization Note** The page states `t < T`; the proof starts at `t = T` (`J*_{T,T} = S_T O`),
so the statement is given for `1 ≤ t ≤ T`. -/
theorem lemma_4_1 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hA : Assumption213 R b)
    (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    LowerSemicontinuous (Jstar R T t) := by sorry

end RiskDistMDP.DPP
