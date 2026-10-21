-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_schmidtHierarchy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.schmidtHierarchy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:57:52.541356+00:00
-- url     : https://prove2.me/theorems/f0c99f76-6400-4033-aa35-d38ce6c02442
-- title:
--   Unnumbered: strict Schmidt hierarchy and separable first class
-- statement:
--   Let $H,K$ be infinite-dimensional separable complex Hilbert spaces. For every positive integer $k$, let $S_k$ be the density states on $H\otimes K$ whose continuous Schmidt number is at most $k$. Then
--
--   $$S_1\subsetneq S_2\subsetneq S_3\subsetneq\cdots,$$
--
--   and every $S_k$ is trace-norm closed and convex. The first class $S_1$ is precisely the separable states, defined as the trace-norm closed convex hull of product density states.
--
--   This asserts strictness at every finite level as well as the identification of the first class.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 7, Unnumbered: strict Schmidt hierarchy and separable first class

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

/-- arXiv:1110.4363v3, PDF p.7, the strict Schmidt hierarchy and its first class.
Both factors are infinite dimensional; closedness and convexity accompany strictness. -/
theorem schmidtHierarchy {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J] :
    (∀ k : ℕ, 0 < k → schmidtClass I J k ⊂ schmidtClass I J (k + 1) ∧
      IsClosed (schmidtClass I J k) ∧ stateConvex (schmidtClass I J k)) ∧
    schmidtClass I J 1 = {rho : State (I × J) | IsSeparable rho.coefficients} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
