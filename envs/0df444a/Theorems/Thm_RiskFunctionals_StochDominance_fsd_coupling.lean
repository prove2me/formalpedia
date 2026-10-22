-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_fsd_coupling
-- name    : RiskFunctionals.StochDominance.fsd_coupling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:34.109856+00:00
-- url     : https://prove2.me/theorems/de016c81-8bc1-4b2a-adff-d29d2778fd00
-- title:
--   Proposition 1.14(i) — the FSD-coupling: $G_1\prec_{FSD}G_2$ gives $Y^{(1)}\le Y^{(2)}$ a.s. with marginals $G_1,G_2$
-- statement:
--   Let $G_1$, $G_2$ be distribution functions on $\mathbb R$ (laws $\mu_1$, $\mu_2$), and suppose $G_1 \prec_{FSD} G_2$, i.e. $\int U\,dG_1 \le \int U\,dG_2$ for every nondecreasing $U$ integrable with respect to both. Then one may construct a pair $Y^{(1)}, Y^{(2)}$ of random variables on a common probability space $(\Omega,\mathcal F,\mathbb P)$ with marginals $G_1$, $G_2$ such that
--   $$Y^{(1)} \le Y^{(2)} \quad \text{a.s.}$$
--
--   The coupling turns the distributional order into a pathwise one; it is the first of the three coupling statements of Proposition 1.14.
--
--   **Formalization Note** "One may construct" is an existence statement: there exist a type $\Omega$ with a $\sigma$-algebra, a probability measure $\mathbb P$ on it, and measurable $Y^{(1)}, Y^{(2)} : \Omega \to \mathbb R$ whose laws (push-forwards of $\mathbb P$) are $\mu_1$ and $\mu_2$, with $Y^{(1)} \le Y^{(2)}$ $\mathbb P$-almost surely.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 18, Proposition 1.14(i)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_Dominance

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- Proposition 1.14(i), the FSD-coupling (Pflug & Römisch, p. 18): if `G₁ ≺_FSD G₂`, then one
may construct a pair `Y⁽¹⁾, Y⁽²⁾` of random variables with marginals `G₁, G₂` such that
`Y⁽¹⁾ ≤ Y⁽²⁾` a.s. -/
theorem fsd_coupling (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : FSD μ₁ μ₂) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y₁ Y₂ : Ω → ℝ), Measurable Y₁ ∧ Measurable Y₂ ∧ P.map Y₁ = μ₁ ∧ P.map Y₂ = μ₂ ∧
      ∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω := by sorry

end RiskFunctionals.StochDominance
