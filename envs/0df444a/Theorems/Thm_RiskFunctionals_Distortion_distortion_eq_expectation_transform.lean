-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_distortion_eq_expectation_transform
-- name    : RiskFunctionals.Distortion.distortion_eq_expectation_transform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:09.950887+00:00
-- url     : https://prove2.me/theorems/e8f0fa53-b19e-4c34-9419-2b869a2669bc
-- title:
--   Eq. (2.69) — $\mathcal A_H(Y)=\mathbb E[Y\,h(G(Y)-V_Y)]$ for differentiable $H$
-- statement:
--   Let $H$ be a distortion function (bounded, right continuous, increasing on $[0,1]$) that is differentiable on $[0,1]$ with derivative $h$, and $H(p)=\int_0^p h(q)\,dq$. Let $Y$ be a random variable with distribution function $G\in\mathcal G_H$, let $U$ be a uniform $[0,1]$ variable independent of $Y$, and let $V_Y=(1-U)[G(Y)-G(Y-)]$ as in (2.68). Then $Y\,h(G(Y)-V_Y)$ is integrable and
--   $$\mathcal A_H(Y)=\mathbb E\big[Y\,h(G(Y)-V_Y)\big]. \tag{2.69}$$
--
--   This writes the distortion functional as a single expectation against a weight that is a function of the generalized quantile transform of $Y$; it is the starting point of the dual representation of Proposition 2.65.
--
--   **Formalization Note** "Differentiable" is one-sided at the endpoints: $H$ has derivative $h(p)$ within $[0,1]$ at every $p\in[0,1]$. $h$ is assumed measurable and Lebesgue integrable on $[0,1]$ (it is a derivative, so measurable on $[0,1]$, and integrable since $H(p)=\int_0^ph$ is finite). $U$ is independent of $Y$, the hypothesis of Proposition 1.3 behind (2.68). $\mathcal A_H(Y)$ is the distortion functional of the law of $Y$; $G\in\mathcal G_H$ is as in the definition file. The statement also asserts that $Y\,h(G(Y)-V_Y)$ is integrable, which the book's expectation presupposes. The book prints $V_Y=(1-U)[G(Y-)-G(Y)]$; with that sign $G(Y)-V_Y=G(Y)+(1-U)[G(Y)-G(Y-)]$, which contradicts the identity in (2.68) at every atom and can exceed $1$, so the sign is a typo and $V_Y=(1-U)[G(Y)-G(Y-)]$ is used, which makes $G(Y)-V_Y$ the generalized quantile transform $(1-U)G(Y-)+UG(Y)$ of Proposition 1.3.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 86, Eq. (2.69)

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders

namespace RiskFunctionals.Distortion

open MeasureTheory ProbabilityTheory

/-- Eq. (2.69) (Pflug & Römisch, p. 86): let `H` be differentiable on `[0, 1]` with derivative
`h`, `H(p) = ∫₀^p h(q) dq`, let `Y` have distribution `G ∈ 𝒢_H`, let `U` be a uniform `[0, 1]`
variable independent of `Y` and `V_Y = (1 − U)[G(Y) − G(Y−)]` as in (2.68) (the book
prints `[G(Y−) − G(Y)]`, a sign typo: only the corrected sign gives the identity of (2.68)). Then
`Y h(G(Y) − V_Y)` is integrable and `𝒜_H(Y) = 𝔼[Y h(G(Y) − V_Y)]`. -/
theorem distortion_eq_expectation_transform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (H : StieltjesFunction ℝ) (h : ℝ → ℝ) (hhm : Measurable h)
    (hhi : IntegrableOn h (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ p ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (h p) (Set.Icc (0 : ℝ) 1) p)
    (hH : ∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ q in (0 : ℝ)..p, h q)
    (Y U : Ω → ℝ) (hY : Measurable Y) (hU : IsUniform01 P U) (hind : IndepFun Y U P)
    (hG : InDistortionDomain H (P.map Y)) :
    Integrable (fun ω => Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω)))) P ∧
    distortionFunctional H (P.map Y) =
      ∫ ω, Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) ∂P := by sorry

end RiskFunctionals.Distortion
