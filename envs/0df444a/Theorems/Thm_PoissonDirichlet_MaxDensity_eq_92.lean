-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_eq_92
-- name    : PoissonDirichlet.MaxDensity.eq_92
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:37.062989+00:00
-- url     : https://prove2.me/theorems/5c454367-24a5-4c27-95cf-0e98ede23ac8
-- title:
--   Display (92), p. 876 — P(V_1 ∈ dx, V_1 = Ṽ_1) = Γ(θ+1)/(Γ(θ+α)Γ(1−α)) x^{−α}(1−x)^{α+θ−1} P_{α,α+θ}(V_1 < x/(1−x)) dx
-- statement:
--   In the setting of Definition 1 ($0 \le \alpha < 1$, $\theta > -\alpha$, $\tilde V$ the stick-breaking sequence, $V$ its ranked values), and with $P_{\alpha,\alpha+\theta}(V_1 < y)$ the distribution function of the largest frequency under $\mathrm{PD}(\alpha, \alpha+\theta)$,
--   $$P_{\alpha,\theta}(V_1 \in dx,\ V_1 = \tilde V_1) = \frac{\Gamma(\theta+1)}{\Gamma(\theta+\alpha)\Gamma(1-\alpha)}\, x^{-\alpha}(1-x)^{\alpha+\theta-1}\,dx\ P_{\alpha,\alpha+\theta}\!\left(V_1 < \frac{x}{1-x}\right)$$
--   on $(0,1)$: for every Borel set $s$, $P(V_1 \in s, V_1 = \tilde V_1)$ is the integral of the right-hand density over $s \cap (0,1)$.
--
--   This is the second computation in the proof of Proposition 19, obtained by conditioning on $\tilde V_1$; together with (91) it yields (52).
--
--   **Formalization Note.** Only the first and last expressions of the printed chain are stated; the middle lines are steps of the proof. The $\mathrm{PD}(\alpha,\alpha+\theta)$ sequence lives on its own probability space $(\Omega', P')$. Probabilities are finite, so `toReal` of $P'(\cdot)$ is exact.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 876, §5.1, proof of Proposition 19, display (92)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Display (92), p. 876 (Pitman–Yor 1997), proof of Proposition 19, first and last
expression. In the setting of Definition 1 (`Ṽ = PoissonDirichlet.Ratio.stick Ỹ`, `V` its PoissonDirichlet.Ratio.ranked values), and with
`V'` a sequence with `PD(α, α + θ)` distribution on another probability space `(Ω', P')`,
`P(V₁ ∈ dx, V₁ = Ṽ₁) = Γ(θ+1)/(Γ(θ+α)Γ(1-α)) x^{-α}(1-x)^{α+θ-1} P'(V'₁ < x/(1-x)) dx`
on `(0, 1)`. -/
theorem eq_92 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P)
    (V' : Ω' → ℕ → ℝ) (hV' : PoissonDirichlet.Ratio.HasPD α (α + θ) P' V')
    (s : Set ℝ) (hs : MeasurableSet s) :
    P {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s ∧
        PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 = PoissonDirichlet.Ratio.stick (fun k => Ytil k ω) 0} =
      ∫⁻ x in s ∩ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal
        (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
          * x ^ (-α) * (1 - x) ^ (α + θ - 1)
          * (P' {ω' | V' ω' 0 < x / (1 - x)}).toReal) := by sorry

end PoissonDirichlet.MaxDensity
