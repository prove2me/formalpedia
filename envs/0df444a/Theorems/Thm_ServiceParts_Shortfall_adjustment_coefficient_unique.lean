-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_adjustment_coefficient_unique
-- name    : ServiceParts.Shortfall.adjustment_coefficient_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:30:05.011553+00:00
-- url     : https://prove2.me/theorems/d3cfd26d-2e9b-440a-b546-640f7311c031
-- title:
--   Theorem 11 (uniqueness part) — E[e^{−α(c−D)}] = 1 has at most one strictly positive root
-- statement:
--   In the capacity-limited system of Section 8.1 (nonnegative i.i.d. demands with $E[D] < c$), the equation
--   $$E\left[e^{-\alpha(c - D)}\right] = 1$$
--   has at most one strictly positive solution: if $\alpha_1 > 0$ and $\alpha_2 > 0$ both solve it, then $\alpha_1 = \alpha_2$.
--
--   This is the uniqueness assertion in the second sentence of Theorem 11; it makes the decay rate $\alpha$ of the shortfall tail well defined.
--
--   **Formalization Note** The expectation is a Bochner integral, which is $0$ when $e^{-\alpha(c-D)}$ is not integrable; such an $\alpha$ therefore never satisfies the hypothesis, so every hypothesis is a genuine solution with finite expectation.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 191, Theorem 11 (second sentence); standing assumption E[D] < c, p. 184

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Theorem 11, second sentence, Muckstadt (2005), p. 191: the equation
`E[e^{−α(c − D)}] = 1` has at most one strictly positive solution `α` (under the standing
assumption `E[D] < c`). The expectation is a Bochner integral; where `e^{−α(c−D)}` is not
integrable it is `0`, so every solution in the hypotheses is a genuine one. -/
theorem adjustment_coefficient_unique {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (α₁ α₂ : ℝ) (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (e₁ : ∫ ω, Real.exp (-α₁ * (M.capacity - M.demand 1 ω)) ∂P = 1)
    (e₂ : ∫ ω, Real.exp (-α₂ * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    α₁ = α₂ := by sorry

end ServiceParts.Shortfall
