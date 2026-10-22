-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_generalized_quantile_transform
-- name    : RiskFunctionals.Distortion.generalized_quantile_transform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:05.789177+00:00
-- url     : https://prove2.me/theorems/1bae79b2-66bc-451b-8e5b-0847bb3fefb3
-- title:
--   Eq. (2.68) — $G(Y)-V_Y=(1-U)G(Y-)+UG(Y)$ is uniformly $[0,1]$ distributed
-- statement:
--   Let $Y$ be a random variable on $(\Omega,\mathcal F,\mathbb P)$ with distribution function $G$, and let $G(u-)=\mathbb P\{Y<u\}$. Let $U$ be a uniform $[0,1]$ random variable independent of $Y$, and set
--   $$V_Y=(1-U)\,[G(Y)-G(Y-)].$$
--   Then the **generalized quantile transform**
--   $$G(Y)-V_Y=(1-U)\,G(Y-)+U\,G(Y) \tag{2.68}$$
--   is uniformly $[0,1]$ distributed.
--
--   When $G$ is continuous this is the classical fact that $G(Y)$ is uniform; at an atom of $Y$ the variable $U$ spreads the jump of $G$ uniformly over $[G(Y-),G(Y)]$. It is the coupling used to represent distortion functionals as expectations.
--
--   **Formalization Note** The page says "for a uniform $[0,1]$ variable $U$" and refers to Proposition 1.3 (p. 7), which assumes $U$ independent of $Y$; that hypothesis is stated here, since without it the conclusion fails. The statement has two parts: the algebraic identity, pointwise on $\Omega$, and uniformity (measurability and law equal to Lebesgue measure on $[0,1]$). The book prints $V_Y=(1-U)[G(Y-)-G(Y)]$; with that sign $G(Y)-V_Y=G(Y)+(1-U)[G(Y)-G(Y-)]$, which contradicts the identity in (2.68) at every atom and can exceed $1$, so the sign is a typo and $V_Y=(1-U)[G(Y)-G(Y-)]$ is used, which makes $G(Y)-V_Y$ the generalized quantile transform $(1-U)G(Y-)+UG(Y)$ of Proposition 1.3.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 86, Eq. (2.68)

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_Orders

namespace RiskFunctionals.Distortion

open MeasureTheory ProbabilityTheory

/-- Eq. (2.68) (Pflug & Römisch, p. 86), the generalized quantile transform of Proposition 1.3
(p. 7): let `Y` have distribution function `G`, let `U` be a uniform `[0, 1]` variable independent
of `Y` (the hypothesis of Proposition 1.3, on which (2.68) rests), and
`V_Y = (1 − U)[G(Y) − G(Y−)]` (the book prints `[G(Y−) − G(Y)]`, a sign typo: with it the
identity below fails at every atom). Then `G(Y) − V_Y = (1 − U)G(Y−) + U G(Y)`, and this variable is
uniformly `[0, 1]` distributed. -/
theorem generalized_quantile_transform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y U : Ω → ℝ) (hY : Measurable Y) (hU : IsUniform01 P U)
    (hind : IndepFun Y U P) :
    (∀ ω, distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω)) =
      (1 - U ω) * distributionFunctionLeft (P.map Y) (Y ω) +
        U ω * distributionFunction (P.map Y) (Y ω)) ∧
    IsUniform01 P (fun ω => distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) := by sorry

end RiskFunctionals.Distortion
