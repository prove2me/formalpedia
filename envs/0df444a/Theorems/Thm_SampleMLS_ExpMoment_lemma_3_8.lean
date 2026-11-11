-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_lemma_3_8
-- name    : SampleMLS.ExpMoment.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:56.866582+00:00
-- url     : https://prove2.me/theorems/4cc21340-f1d7-4232-b1c1-6fe7b49c3838
-- title:
--   Lemma 3.8 — threshold selection: some integer θ ≤ Θ has Pr[ξ ≤ θ]2^{−θ} ≥ E[2^{−ξ}]/(4(Θ+1)), and Pr[ξ ≤ θ]2^{−θ} ≤ E[2^{−ξ}] for every integer θ
-- statement:
--   Let $\xi$ be a random variable with values in $[0,\infty]$ on a probability space, with $\Pr[\xi<\infty]>0$. Then $E[2^{-\xi}]>0$ (with $2^{-\infty}=0$), and:
--
--   (a) for every integer $\Theta\ge0$ with $2^{-\Theta}\le E[2^{-\xi}]/2$, some $\theta\in\{0,\dots,\Theta\}$ satisfies $\Pr[\xi\le\theta]\,2^{-\theta}\ge E[2^{-\xi}]/(4(\Theta+1))$;
--
--   (b) $\Pr[\xi\le\theta]\,2^{-\theta}\le E[2^{-\xi}]$ for every integer $\theta$ (also negative).
--
--   Differences from the source:
--   - encoding: a random variable ξ with values in [0, ∞], E[2^{−ξ}], Pr[ξ ≤ θ] → a measurable ξ : Ω → ℝ≥0∞ on a probability measure μ; E[2^{−ξ}] = ∫⁻ twoNeg ∘ ξ dμ with twoNeg ⊤ = 0; Pr[ξ ≤ θ] = probLe μ ξ θ = μ{ξ ≠ ⊤ ∧ ξ.toReal ≤ θ}; probabilities and expectations in ℝ≥0∞; reason: the same numbers: the lower Lebesgue integral of a measurable [0,1]-valued function is its expectation
--   - encoding: an integer Θ ≥ 0 and θ ∈ {0, …, Θ} in (a) → Θ θ : ℕ with θ ≤ Θ; reason: the same integers
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), Lemma 3.8, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Lemma 3.8 (Threshold selection), p. 18 (PDF 20). For a random variable `ξ` with values in
`[0, ∞]` and `Pr[ξ < ∞] > 0`: `E[2^{−ξ}] > 0`; (a) if `Θ ≥ 0` is an integer with
`2^{−Θ} ≤ E[2^{−ξ}]/2`, some `θ ∈ {0, …, Θ}` has `Pr[ξ ≤ θ] 2^{−θ} ≥ E[2^{−ξ}]/(4(Θ + 1))`;
(b) `Pr[ξ ≤ θ] 2^{−θ} ≤ E[2^{−ξ}]` for every integer `θ`. -/
theorem lemma_3_8 {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ξ : Ω → ℝ≥0∞) (hξ : Measurable ξ)
    (hfin : 0 < μ {ω | ξ ω < ⊤}) :
    0 < (∫⁻ ω, twoNeg (ξ ω) ∂μ) ∧
    (∀ Θ : ℕ, (2 : ℝ≥0∞) ^ (-(Θ : ℤ)) ≤ (∫⁻ ω, twoNeg (ξ ω) ∂μ) / 2 →
      ∃ θ : ℕ, θ ≤ Θ ∧
        (∫⁻ ω, twoNeg (ξ ω) ∂μ) / (4 * ((Θ : ℝ≥0∞) + 1)) ≤
          probLe μ ξ (θ : ℤ) * (2 : ℝ≥0∞) ^ (-(θ : ℤ))) ∧
    (∀ θ : ℤ, probLe μ ξ θ * (2 : ℝ≥0∞) ^ (-θ) ≤ ∫⁻ ω, twoNeg (ξ ω) ∂μ) := by sorry

end SampleMLS.ExpMoment
