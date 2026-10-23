-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_ccd_iff_lorenz
-- name    : RiskFunctionals.StochDominance.ccd_iff_lorenz
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:25.745571+00:00
-- url     : https://prove2.me/theorems/c09758e1-9bab-4821-9954-fb2bbf278c60
-- title:
--   Proposition 1.16 — concave dominance via Lorenz curves and equal means
-- statement:
--   Let $G_1$, $G_2$ be distribution functions on $\mathbb R$ with finite expectations $\mathbb E\{G_1\}$, $\mathbb E\{G_2\}$, both nonzero, and let
--   $$L_{G_i}(p) = \frac{\mathcal G_i^{[-1]}(p)}{\mathbb E\{G_i\}}, \qquad \mathcal G_i^{[-1]}(p) = \int_0^p G_i^{-1}(q)\,dq,$$
--   be their Lorenz curves. Then
--   $$G_1 \prec_{CCD} G_2 \quad\Longleftrightarrow\quad L_{G_1}(p) \le L_{G_2}(p) \ \text{ for all } p \in (0,1) \ \text{ and } \ \mathbb E\{G_1\} = \mathbb E\{G_2\}.$$
--   Here $\prec_{CCD}$ is concave dominance (Definition 1.10(iii)): $\int U\,dG_1 \le \int U\,dG_2$ for every concave $U$ integrable with respect to both.
--
--   The proposition is the reason the convex order is also called Lorenz dominance.
--
--   **Formalization Note** The book prints the comparison as $L_{G_1}(p) \le L_{G_1}(p)$, which is an evident typo (it compares a curve with itself); it is formalized as the intended $L_{G_1}(p) \le L_{G_2}(p)$. The Lorenz curve $L_G = \mathcal G^{[-1]}(p)/\mathcal G^{[-1]}(1)$ of Definition 1.15 is a quotient by the mean, so the hypotheses $\mathbb E\{G_1\}\ne 0$, $\mathbb E\{G_2\}\ne0$ are made explicit (Lean's real division by $0$ would return $0$). The finite expectations are integrability of the identity under $\mu_1$, $\mu_2$. See finding F2 for the sign of the mean.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 19, Proposition 1.16 (with Definition 1.15)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions
import Definitions.Def_RiskFunctionals_StochDominance_Dominance

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- Proposition 1.16 (Pflug & Römisch, p. 19), with the printed `L_{G₁}(p) ≤ L_{G₁}(p)` read as
the intended `L_{G₁}(p) ≤ L_{G₂}(p)`: for distributions with finite, nonzero expectations
(so that the Lorenz curves of Definition 1.15 are defined), `G₁ ≺_CCD G₂` iff
`L_{G₁}(p) ≤ L_{G₂}(p)` for all `p ∈ (0,1)` and `𝔼{G₁} = 𝔼{G₂}`. -/
theorem ccd_iff_lorenz (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : Integrable (fun v : ℝ => v) μ₁) (h₂ : Integrable (fun v : ℝ => v) μ₂)
    (hm₁ : ∫ v, v ∂μ₁ ≠ 0) (hm₂ : ∫ v, v ∂μ₂ ≠ 0) :
    CCD μ₁ μ₂ ↔ (∀ p ∈ Set.Ioo (0 : ℝ) 1, lorenzCurve μ₁ p ≤ lorenzCurve μ₂ p) ∧
      ∫ v, v ∂μ₁ = ∫ v, v ∂μ₂ := by sorry

end RiskFunctionals.StochDominance
