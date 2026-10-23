-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_entropy_continuous_closed_hull
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.entropy_continuous_closed_hull
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:36:29.591007+00:00
-- url     : https://prove2.me/theorems/44817eb8-5084-4655-ba33-64d4d3d25126
-- title:
--   Corollary 2
-- statement:
--   Let $A$ be a closed set of density states on which entropy is finite and continuous. Suppose a density state $\sigma$ makes $D(\rho\|\sigma)$ finite, continuous, and bounded for $\rho\in A$. Then
--
--   $$H\big|_{\overline{\operatorname{co}}A}\ \text{is finite and continuous}.$$
--
--   The reference-relative-entropy hypothesis controls passage to the closed convex hull.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 20, Corollary 2

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

/-- Corollary 2, arXiv:quant-ph/0510073v2, PDF pp.20.
 -/
theorem entropy_continuous_closed_hull {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hclosed : IsClosed A)
    (hentropy : FiniteContinuousOn stateEntropyNats A)
    (href : ∃ sigma : State I,
      FiniteContinuousOn (fun rho => stateRelativeEntropyNats rho sigma) A ∧
        (⨆ rho : A, stateRelativeEntropyNats rho.val sigma) < ⊤) :
    FiniteContinuousOn stateEntropyNats (stateClosedConvexHull A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
