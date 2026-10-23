-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_choquet_integral_formula
-- name    : RiskFunctionals.Distortion.choquet_integral_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:50.148117+00:00
-- url     : https://prove2.me/theorems/0bd1b290-dd4b-415e-9f70-d0f6ae825eeb
-- title:
--   Lemma 2.62 — $\int G^{-1}\,dH=-\int_{-\infty}^0 H(G(u))\,du+\int_0^\infty\bar H(1-G(u))\,du$
-- statement:
--   Let $H$ be a bounded, right continuous, increasing function on $[0,1]$, the distribution function of a non-negative measure $dH$ on $[0,1]$, and let $G$ be a distribution function with quantile function $G^{-1}$ that belongs to $\mathcal G_H$, i.e. $G^{-1}$ is $dH$ integrable. Write $\bar H(u)=H(1)-H(1-u)$. Then $u\mapsto H(G(u))$ is integrable on $(-\infty,0]$, $u\mapsto\bar H(1-G(u))$ is integrable on $(0,\infty)$, and
--   $$\int_0^1 G^{-1}(p)\,dH(p)=-\int_{-\infty}^0 H(G(u))\,du+\int_0^\infty \bar H(1-G(u))\,du. \tag{2.65}$$
--
--   For $H(p)=p$ this is the partial integration formula $\mathbb E(Y)=-\int_{-\infty}^0G(u)\,du+\int_0^\infty(1-G(u))\,du$; in general it expresses the distortion functional $\mathcal A_H\{G\}$ as a Choquet integral, the form used for insurance premia.
--
--   **Formalization Note** The book prints the limits of the left-hand integral as $-\infty$ and $\infty$; the integral is the distortion functional (2.64), over $[0,1]$ against $dH$, and is stated so. The right-hand side needs $H(0)=0$ (otherwise $\int_{-\infty}^0 H(G(u))\,du$ diverges); this is part of $G\in\mathcal G_H$ in the definition file, because $dH$ puts mass $H(0)$ on $p=0$, where $G^{-1}(0)=-\infty$. The integrals on the right are Lebesgue integrals over $(-\infty,0]$ and $(0,\infty)$, and their existence (which the formula presupposes) is part of the conclusion; $H$ is a Mathlib `StieltjesFunction` whose values on $[0,1]$ are used.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 81, Lemma 2.62

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- Lemma 2.62 (Pflug & Römisch, p. 81, (2.65)): for `G ∈ 𝒢_H`,
`∫₀¹ G⁻¹(p) dH(p) = −∫_{−∞}^0 H(G(u)) du + ∫_0^∞ H̄(1 − G(u)) du` with `H̄(u) = H(1) − H(1 − u)`.
The book prints the limits of the left integral as `−∞, ∞`; the integral is `𝒜_H{G}` of (2.64),
over `[0, 1]` against `dH`. `G ∈ 𝒢_H` includes `H(0) = 0` (see `InDistortionDomain`). Both integrals on the right exist
(their integrands are integrable), which the formula presupposes. -/
theorem choquet_integral_formula (H : StieltjesFunction ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hG : InDistortionDomain H μ) :
    IntegrableOn (fun u => H (distributionFunction μ u)) (Set.Iic (0 : ℝ)) ∧
    IntegrableOn (fun u => distortionBar H (1 - distributionFunction μ u)) (Set.Ioi (0 : ℝ)) ∧
    distortionFunctional H μ =
      -(∫ u in Set.Iic (0 : ℝ), H (distributionFunction μ u)) +
        ∫ u in Set.Ioi (0 : ℝ), distortionBar H (1 - distributionFunction μ u) := by sorry

end RiskFunctionals.Distortion
