-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_eq_6
-- name    : PoissonDirichlet.MaxDensity.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:09.819922+00:00
-- url     : https://prove2.me/theorems/bc6ac879-2631-4efb-bd0b-0d09b9d3282b
-- title:
--   Display (6), p. 858 — E ∑ f(V_n) = E[f(Ṽ_1)/Ṽ_1] = Γ(θ+1)/(Γ(θ+α)Γ(1−α)) ∫₀¹ f(u)(1−u)^{α+θ−1}u^{−α−1} du
-- statement:
--   Let $0 \le \alpha < 1$, $\theta > -\alpha$, and let $(V_n)$ have the $\mathrm{PD}(\alpha,\theta)$ distribution. For every measurable $f : \mathbb R \to [0,\infty]$,
--   $$E \sum_{n=1}^\infty f(V_n) = E\left[\frac{f(\tilde V_1)}{\tilde V_1}\right] = \frac{\Gamma(\theta+1)}{\Gamma(\theta+\alpha)\Gamma(1-\alpha)} \int_0^1 f(u)\,\frac{(1-u)^{\alpha+\theta-1}}{u^{\alpha+1}}\,du,$$
--   where $\tilde V_1$ is any size-biased pick from $(V_n)$.
--
--   The formula computes the mean of every additive functional of the ranked frequencies; with $f$ the indicator of a set in $(1/2, 1)$ it already gives the density of $V_1$ there, the base case of the recursion behind Proposition 19.
--
--   **Formalization Note.** Expectations are lower Lebesgue integrals of $[0,\infty]$-valued functions, so no integrability hypothesis is needed and none is hidden. The first equality is stated for every size-biased pick $W$ of $V$ on the same space.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 858, display (6)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Display (6), p. 858 (Pitman–Yor 1997). For `(Vₙ)` with `PD(α, θ)` distribution,
`0 ≤ α < 1`, `θ > -α`, and every measurable `f ≥ 0`,
`E ∑ₙ f(Vₙ) = E[f(Ṽ₁)/Ṽ₁] = Γ(θ+1)/(Γ(θ+α)Γ(1-α)) ∫₀¹ f(u)(1-u)^{α+θ-1}/u^{α+1} du`,
where `Ṽ₁` is any size-biased pick from `(Vₙ)`. Expectations are lower Lebesgue integrals
of `[0, ∞]`-valued functions. -/
theorem eq_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V) (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ ω, ∑' k, f (V ω k) ∂P =
        ∫⁻ u in Set.Ioo (0 : ℝ) 1, f u * ENNReal.ofReal
          (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
            * (1 - u) ^ (α + θ - 1) / u ^ (α + 1))) ∧
      ∀ W : Ω → ℝ, IsSizeBiasedPick P V W →
        ∫⁻ ω, ∑' k, f (V ω k) ∂P = ∫⁻ ω, f (W ω) / ENNReal.ofReal (W ω) ∂P := by sorry

end PoissonDirichlet.MaxDensity
