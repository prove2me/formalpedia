-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_quantile_transform
-- name    : RiskFunctionals.StochDominance.quantile_transform
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:34.661908+00:00
-- url     : https://prove2.me/theorems/5cc017c1-a22a-40b4-873b-beac0728e693
-- title:
--   Proposition 1.2 — the quantile transform: $G^{-1}(U)$ has distribution $G$
-- statement:
--   Let $Y$ be a real random variable with distribution function $G$ and law $\mu$, and let $G^{-1}$ be its quantile function. Let $U$ be a random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ that is uniformly distributed on $[0,1]$. Then $G^{-1}(U)$ has the same distribution as $Y$:
--   $$\mathbb P\{G^{-1}(U) \le v\} = G(v) \quad \text{for all } v\in\mathbb R, \qquad\text{i.e.}\qquad \mathcal L\big(G^{-1}(U)\big) = \mu .$$
--
--   The quantile transform realizes every distribution on the unit interval; it is the basic device for constructing couplings with prescribed marginals.
--
--   **Formalization Note** The law of $Y$ enters as the probability measure $\mu$ on $\mathbb R$. "Uniform on $[0,1]$" is the hypothesis that the push-forward of $\mathbb P$ under the measurable map $U$ is Lebesgue measure restricted to $[0,1]$; the conclusion is the equality of the push-forward of $\mathbb P$ under $\omega \mapsto G^{-1}(U(\omega))$ with $\mu$. The values of $G^{-1}$ at the endpoints $0$ and $1$ (junk in Lean, $\pm\infty$ or undefined in the book) are taken on a null set and do not matter.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 7, Proposition 1.2

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- Proposition 1.2, the quantile transform (Pflug & Römisch, p. 7): let `Y` have distribution
function `G` (law `μ`). If `U` is a uniform `[0,1]` random variable, then `G⁻¹(U)` has the same
distribution as `Y`. -/
theorem quantile_transform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (hunif : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (fun ω => quantileFunction μ (U ω)) = μ := by sorry

end RiskFunctionals.StochDominance
