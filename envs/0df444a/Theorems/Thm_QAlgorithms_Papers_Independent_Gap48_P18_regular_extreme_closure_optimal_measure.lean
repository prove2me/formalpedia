-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_regular_extreme_closure_optimal_measure
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.regular_extreme_closure_optimal_measure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:43:17.697002+00:00
-- url     : https://prove2.me/theorems/ca1df92c-3633-4236-ac81-50ab48d944bd
-- title:
--   Theorem 3
-- statement:
--   Let $A$ be nonempty, closed, and convex with finite capacity. If the closure of its extreme points is regular in the sense of Definition 2, then there exists a law $\mu_*$ such that
--
--   $$\chi(\mu_*)=\bar C(A),\qquad\mu_*\big(\overline{\mathrm{Ext}(A)}\big)=1.$$
--
--   Regularity supplies a sufficient condition for an optimal measure supported on the closure of the extreme boundary.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 40, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, arXiv:quant-ph/0510073v2, PDF pp.40.
PDF overlines verified by rendering p.40; support is on closure of Ext(A). -/
theorem regular_extreme_closure_optimal_measure {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hconvex : CoefficientConvexStates A) (hfinite : setChiCapacity A < ⊤)
    (hregular : ChiRegular (extremeClosure A)) :
    ∃ mu : GeneralizedEnsemble I, OptimalMeasure A mu ∧
      MeasureConcentratedOn (mu : Measure (State I)) (extremeClosure A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
