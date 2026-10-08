-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_eq_91
-- name    : PoissonDirichlet.MaxDensity.eq_91
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:36.530335+00:00
-- url     : https://prove2.me/theorems/38712f76-63af-4912-8e6e-71f303e56657
-- title:
--   Display (91), p. 876 — P(V_1 ∈ dx, V_1 = Ṽ_1) = x P(V_1 ∈ dx)
-- statement:
--   In the setting of Definition 1 ($0 \le \alpha < 1$, $\theta > -\alpha$, $\tilde Y_n \sim \mathrm{beta}(1-\alpha,\theta+n\alpha)$ independent, $\tilde V$ the stick-breaking sequence, $V$ its ranked values),
--   $$P_{\alpha,\theta}(V_1 \in dx,\ V_1 = \tilde V_1) = x\,P_{\alpha,\theta}(V_1 \in dx),$$
--   that is, for every Borel set $s \subseteq \mathbb R$,
--   $$P(V_1 \in s,\ V_1 = \tilde V_1) = E\big[V_1;\ V_1 \in s\big].$$
--
--   This is the first of the two computations of the same quantity whose comparison gives (52): the first piece of the stick is the largest one with conditional probability $V_1$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 876, §5.1, proof of Proposition 19, display (91)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Display (91), p. 876 (Pitman–Yor 1997), proof of Proposition 19. In the setting of
Definition 1 (`Ṽ = PoissonDirichlet.Ratio.stick Ỹ`, `V` its PoissonDirichlet.Ratio.ranked values),
`P(V₁ ∈ dx, V₁ = Ṽ₁) = x P(V₁ ∈ dx)`, i.e. for every Borel set `s`,
`P(V₁ ∈ s, V₁ = Ṽ₁) = E[V₁; V₁ ∈ s]`. -/
theorem eq_91 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P)
    (s : Set ℝ) (hs : MeasurableSet s) :
    P {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s ∧
        PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 = PoissonDirichlet.Ratio.stick (fun k => Ytil k ω) 0} =
      ∫⁻ ω in {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s},
        ENNReal.ofReal (PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0) ∂P := by sorry

end PoissonDirichlet.MaxDensity
