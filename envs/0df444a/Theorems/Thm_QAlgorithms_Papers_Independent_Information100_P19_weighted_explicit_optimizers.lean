-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_weighted_explicit_optimizers
-- name    : QAlgorithms.Papers.Independent.Information100.P19.weighted_explicit_optimizers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:08:06.63044+00:00
-- url     : https://prove2.me/theorems/55df834b-a244-4510-8549-f0eafd37e77f
-- title:
--   Appendix A unnumbered: explicit weighted optimizers
-- statement:
--   For every $0\le\beta<3/2$, the degree-one and degree-two weighted optimizers include $x$ and $3x/2-x^2/2$. The following exact polynomials are weighted optimizers at the indicated parameters:
--   $$h_{3,1}=(1/4+3\sqrt3/2)x-(3/2+3\sqrt3/2)x^2+9x^3/4,$$
--   $$h_{4,1}=185x/54-137x^2/18+76x^3/9-88x^4/27,$$
--   $$h_{3,0}=(1+\sqrt2)x-(4-\sqrt2)x^2+(4-2\sqrt2)x^3.$$
--   Their interior contacts with $\sqrt x$ occur at $1/3,1/4,1/2$, respectively; $h_{4,1}$ is also tangent at $1$. Membership in the actual integral argmin is asserted, rather than defining a selected optimizer to have these values.
--
--   An optimizer minimizes $\int_0^1x^{-\beta}(\sqrt x-h(x))\,dx$ among real polynomials of degree at most the stated order, with zero constant term, $h(1)=1$, and $h(x)\le\sqrt x$ on $[0,1]$.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 52, Appendix A unnumbered: explicit weighted optimizers

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Appendix A unnumbered: explicit weighted optimizers; arXiv:2609.29471v1, PDF pp.52. -/
theorem weighted_explicit_optimizers  :
    (∀ beta : ℝ, 0≤beta → beta<3/2 →
      WeightedOptimizer 1 beta Polynomial.X ∧
      WeightedOptimizer 2 beta ((3/2:ℝ) • Polynomial.X-(1/2:ℝ) • Polynomial.X^2)) ∧
    (let h3 : Polynomial ℝ :=
       (1/4+3*Real.sqrt 3/2) • Polynomial.X -
       (3/2+3*Real.sqrt 3/2) • Polynomial.X^2 + (9/4:ℝ) • Polynomial.X^3
     let h4 : Polynomial ℝ := (185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4
     let h30 : Polynomial ℝ := (1+Real.sqrt 2) • Polynomial.X -
       (4-Real.sqrt 2) • Polynomial.X^2 + (4-2*Real.sqrt 2) • Polynomial.X^3
     WeightedOptimizer 3 1 h3 ∧ WeightedOptimizer 4 1 h4 ∧ WeightedOptimizer 3 0 h30 ∧
       h3.eval (1/3)=Real.sqrt (1/3) ∧ h4.eval (1/4)=Real.sqrt (1/4) ∧
       h4.derivative.eval 1=1/2 ∧ h30.eval (1/2)=Real.sqrt (1/2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
