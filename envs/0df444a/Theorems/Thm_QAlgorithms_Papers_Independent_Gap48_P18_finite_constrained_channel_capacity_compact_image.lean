-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_finite_constrained_channel_capacity_compact_image
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.finite_constrained_channel_capacity_compact_image
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:40:32.430702+00:00
-- url     : https://prove2.me/theorems/a7f11fbd-0717-4ad8-b894-01de66a38ed3
-- title:
--   Corollary 10
-- statement:
--   Let H and K be nonzero separable complex Hilbert spaces, Phi a quantum channel from H to K, and A a convex set of normalized input states. Let Cbar(Phi,A) be the supremum of output Holevo information over finite input ensembles whose average lies in A. If Cbar(Phi,A)<infinity, then Phi(A) is relatively compact in trace norm. The explicit convexity guard corrects the printed arbitrary-subset domain.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 36, Corollary 10

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

/-- Corollary 10, arXiv:quant-ph/0510073v2, PDF p.36, corrected domain.
Printed: arbitrary input subset A with finite average-constrained capacity.
Changed: explicitly require A convex; retain the same capacity and conclusion.
Why: for the identity channel, the noncompact set of orthogonal pure states has
average-constrained capacity zero. Convexity makes every finite ensemble of
signals in A admissible, which is exactly what the printed proof's inequality needs.
The correction is nonvacuous, including convex singletons and energy sublevels. -/
theorem finite_constrained_channel_capacity_compact_image {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : StateChannel I J) (A : Set (State I))
    (hconvex : CoefficientConvexStates A)
    (hfinite : finiteEnsembleCapacity Phi.map A < ⊤) :
    IsCompact (closure (Phi.action '' A)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
