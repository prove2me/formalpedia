-- Prove2me | Theorems.Thm_SuperPareto_lemma_2
-- name    : SuperPareto.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:27.039254+00:00
-- url     : https://prove2.me/theorems/dc17afca-8a0f-4e7d-bc60-3886098bfb2c
-- title:
--   Lemma 2, p.9 — $Y\le_{\mathrm{st}}\sum\theta_iY_i$ implies $f(Y)\le_{\mathrm{st}}\sum\theta_if(Y_i)$
-- statement:
--   Let $Y,Y_1,\dots,Y_n$ be any real random variables on one probability space and $(\theta_1,\dots,\theta_n)\in\Delta_n$. If
--
--   $$
--   Y\le_{\mathrm{st}}\sum_{i=1}^n\theta_iY_i,
--   $$
--
--   then for every increasing convex function $f$,
--
--   $$
--   f(Y)\le_{\mathrm{st}}\sum_{i=1}^n\theta_if(Y_i).
--   $$
--
--   Here $U\le_{\mathrm{st}}V$ means $P(U\le x)\ge P(V\le x)$ for all $x\in\mathbb R$. The lemma transfers the diversification penalty from Pareto(1) losses to their increasing convex transforms, i.e. to super-Pareto losses.
--
--   **Formalization Note** $U\le_{\mathrm{st}}V$ is the platform definition `StarShapedRisk.LawInvariant.FSD P U V` (note the argument order). $\Delta_n$ is Mathlib's `stdSimplex ℝ ι`.
--
--   Differences from the source:
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Lemma 2, p.9 (proof in Appendix A, p.14)

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Lemma 2: dominance passes through increasing convex functions.** Chen, Embrechts, Wang,
*An unexpected stochastic dominance*, arXiv:2208.08471v4, Lemma 2, p.9: let `Y, Y₁, …, Yₙ` be any
random variables and `(θ₁, …, θₙ) ∈ Δₙ`. If `Y ≤st ∑ θᵢYᵢ`, then `f(Y) ≤st ∑ θᵢ f(Yᵢ)` for any
increasing convex function `f`.

**Formalization Note.** `X ≤st Z` (first-order stochastic dominance, p.2: `P(X ≤ x) ≥ P(Z ≤ x)` for
all `x`) is the platform's `StarShapedRisk.LawInvariant.FSD P X Z`; note the argument order:
`FSD P X Z` means `X ≤st Z`. `Δₙ` is Mathlib's `stdSimplex ℝ ι`; `f : ℝ → ℝ` is `Monotone` and
`ConvexOn ℝ univ`. -/
theorem lemma_2 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (Y : Ω → ℝ) (Ys : ι → Ω → ℝ) (hY : Measurable Y) (hYs : ∀ i, Measurable (Ys i))
    (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι)
    (hdom : StarShapedRisk.LawInvariant.FSD P Y (fun ω => ∑ i, θ i * Ys i ω))
    (f : ℝ → ℝ) (hfmono : Monotone f) (hfconv : ConvexOn ℝ Set.univ f) :
    StarShapedRisk.LawInvariant.FSD P (fun ω => f (Y ω))
      (fun ω => ∑ i, θ i * f (Ys i ω)) := by sorry

end SuperPareto
