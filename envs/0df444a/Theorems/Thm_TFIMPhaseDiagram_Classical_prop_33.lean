-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_33
-- name    : TFIMPhaseDiagram.Classical.prop_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:02.327656+00:00
-- url     : https://prove2.me/theorems/3a36ac39-62d6-43d0-b11b-ccfd372810b8
-- title:
--   Proposition 33 — Product-of-sample-means estimate with success 3/4
-- statement:
--   Let $W_1,\ldots,W_\ell$ be independent, strictly positive random variables with finite second moments and $\mathbb E[W_i^2]/\mathbb E[W_i]^2\le B$. For $0<\epsilon<1$, take $m=\lceil16B\ell/\epsilon^2\rceil$ mutually independent samples of each variable, and let $S_i$ be their mean. Then
--   $$\Pr\left[(1-\epsilon)\mathbb E\!\left[\prod_iW_i\right]\le\prod_i S_i\le(1+\epsilon)\mathbb E\!\left[\prod_iW_i\right]\right]\ge\tfrac34.$$
--   The variables live on arbitrary probability spaces. This is the positive product estimator used in annealing, with the exact sample count and success probability.
--
--   Differences from the source:
--   - encoding: positive random variables with the displayed finite second-moment ratio → measurable positive random variables with integrable squares and identically distributed independent sample arrays; reason: The ratio presupposes finite moments; no tail or bounded-support condition is added.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.29 = PDF p.29, Proposition 33

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 33, p.29: arbitrary positive independent variables with finite second moments. -/
theorem prop_33 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℓ : ℕ) (W : Fin ℓ → Ω → ℝ) (hW : ∀ i, Measurable (W i))
    (hpos : ∀ i, ∀ᵐ ω ∂μ, 0 < W i ω)
    (hmoment : ∀ i, Integrable (fun ω => (W i ω)^2) μ)
    (hind : iIndepFun W μ) (B ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hB : ∀ i, (∫ ω, (W i ω)^2 ∂μ) / (∫ ω, W i ω ∂μ)^2 ≤ B)
    (X : Fin ℓ → Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ → Ξ → ℝ)
    (hX : iIndepFun (fun ij : Fin ℓ × Fin ⌈16*B*(ℓ : ℝ)/ε^2⌉₊ => X ij.1 ij.2) ν)
    (hlaw : ∀ i j, IdentDistrib (X i j) (W i) ν μ) :
  let m := ⌈16*B*(ℓ : ℝ)/ε^2⌉₊
  let estimate := fun ξ => ∏ i, ((∑ j, X i j ξ) / (m : ℝ))
  3/4 ≤ ν.real {ξ | (1-ε) * (∫ ω, ∏ i, W i ω ∂μ) ≤ estimate ξ ∧
    estimate ξ ≤ (1+ε) * (∫ ω, ∏ i, W i ω ∂μ)} := by sorry
end TFIMPhaseDiagram.Classical
