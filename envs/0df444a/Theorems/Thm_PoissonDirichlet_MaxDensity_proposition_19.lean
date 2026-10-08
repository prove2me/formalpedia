-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_proposition_19
-- name    : PoissonDirichlet.MaxDensity.proposition_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:34.694094+00:00
-- url     : https://prove2.me/theorems/c564052d-9a05-454c-a7cd-1f9fb68de640
-- title:
--   Proposition 19, p. 867 — the PD(α, θ) density of V_1 is Γ(θ+1)/(Γ(θ+α)Γ(1−α)) x^{−α−1}(1−x)^{α+θ−1} P_{α,α+θ}(V_1 < x/(1−x))
-- statement:
--   Let $0 \le \alpha < 1$ and $\theta > -\alpha$. Let $(V_n)$ have the $\mathrm{PD}(\alpha,\theta)$ distribution under $P_{\alpha,\theta}$, and write $P_{\alpha,\alpha+\theta}(V_1 < y)$ for the distribution function of the largest frequency under $\mathrm{PD}(\alpha,\alpha+\theta)$. Then $V_1 \in (0,1)$ almost surely, and the law of $V_1$ has the density
--   $$\frac{P_{\alpha,\theta}(V_1 \in dx)}{dx} = \frac{\Gamma(\theta+1)}{\Gamma(\theta+\alpha)\Gamma(1-\alpha)}\, x^{-\alpha-1}(1-x)^{\alpha+\theta-1} \times P_{\alpha,\alpha+\theta}\!\left(V_1 < \frac{x}{1-x}\right) \qquad (0 < x < 1).$$
--
--   The law of the largest frequency of $\mathrm{PD}(\alpha,\theta)$ has no closed form; (52) expresses it through the same law at the shifted parameter $\alpha+\theta$. For $1/2 < x < 1$ the last factor is $1$, and recursion determines the density on every interval $(1/(n+1), 1/n)$. The special case $\alpha = 0$, $\theta = 1$ appears as equation (3) of Vershik, attributed to Dickman.
--
--   **Formalization Note.** The density identity is stated as an equality of measures: $P(V_1 \in s)$ equals the integral of the density over $s$, for every Borel $s \subseteq (0,1)$, together with $P(V_1 \in (0,1)) = 1$; no pointwise Radon–Nikodym derivative is used. The two laws live on two probability spaces $(\Omega, P)$ and $(\Omega', P')$. The uniqueness clause of the proposition is the separate statement `proposition_19_unique`.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 867, Proposition 19, display (52)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proposition 19, p. 867 (Pitman–Yor 1997), identity (52). For `0 ≤ α < 1`, `θ > -α`, let
`V` have `PD(α, θ)` distribution under `P` and `V'` have `PD(α, α + θ)` distribution under
`P'`. Then `V₁` lies in `(0, 1)` almost surely and its law has density
`Γ(θ+1)/(Γ(θ+α)Γ(1-α)) x^{-α-1}(1-x)^{α+θ-1} P'(V'₁ < x/(1-x))` on `(0, 1)`.
(0-based: `V ω 0` is `V₁`.) -/
theorem proposition_19 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V) (V' : Ω' → ℕ → ℝ) (hV' : PoissonDirichlet.Ratio.HasPD α (α + θ) P' V') :
    P {ω | V ω 0 ∈ Set.Ioo (0 : ℝ) 1} = 1 ∧
      ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
        P {ω | V ω 0 ∈ s} =
          ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (P' {ω' | V' ω' 0 < x / (1 - x)}).toReal) := by sorry

end PoissonDirichlet.MaxDensity
