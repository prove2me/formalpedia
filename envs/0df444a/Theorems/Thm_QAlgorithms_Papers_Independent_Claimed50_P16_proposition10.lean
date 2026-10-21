-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition10
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:55:19.231143+00:00
-- url     : https://prove2.me/theorems/4fce0118-42c3-4000-8cf0-964be89de5ea
-- title:
--   Proposition 10: lower-semicontinuous essential-supremum roof
-- statement:
--   Let $H$ be a separable complex Hilbert space, $A$ a trace-norm closed subset of its density states, and $f:A\to[0,\infty]$ lower semicontinuous. For $\rho$ in the trace-norm closed convex hull $\overline{\operatorname{co}}A$, let $\mathcal P_\rho(A)$ be its Borel barycentric fiber and put
--
--   $$F(\rho)=\inf_{\mu\in\mathcal P_\rho(A)}\operatorname*{ess\,sup}_{\mu}f.$$
--
--   Then $F$ is lower semicontinuous on this hull and the infimum is attained at an extreme point of the fixed-barycenter fiber. For every finite $c\ge0$,
--
--   $$\{\rho\in\overline{\operatorname{co}}A:F(\rho)\le c\}=\overline{\operatorname{co}}\{\rho\in A:f(\rho)\le c\}.$$
--
--   The empty set has empty hull, so it supplies no spurious state with roof zero. Extended values are necessary for the application to Schmidt rank.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 13, Proposition 10: lower-semicontinuous essential-supremum roof

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.13–14, Proposition 10. Nonnegative functions may
be infinity-valued (as required for its application to Schmidt rank). Lower
semicontinuity is expressed by closed sublevels, including on the hull subtype.
The infimum is attained in an extreme fixed-barycenter fiber; A may be empty. -/
theorem proposition10 {I : Type} [Countable I] (A : Set (State I)) (hA : IsTraceClosed A)
    (f : A → ℝ≥0∞) (hf : ∀ c : ℝ≥0∞, IsClosed {x : A | f x ≤ c}) :
    (∀ c : ℝ≥0∞, IsClosed {rho : stateHull A | roof A f rho.val ≤ c}) ∧
    (∀ rho ∈ stateHull A, ∃ mu : Measure A,
      extremeFiber rho mu ∧ essSup f mu = roof A f rho) ∧
    (∀ c : ℝ≥0, {rho : State I | rho ∈ stateHull A ∧ roof A f rho ≤ (c : ℝ≥0∞)} =
      stateHull (Subtype.val '' {x : A | f x ≤ (c : ℝ≥0∞)})) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
