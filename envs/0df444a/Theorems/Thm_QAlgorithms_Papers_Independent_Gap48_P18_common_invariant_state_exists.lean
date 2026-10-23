-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_common_invariant_state_exists
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.common_invariant_state_exists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:49:29.771361+00:00
-- url     : https://prove2.me/theorems/3e1f0c93-b817-4e42-996d-0c39ae260900
-- title:
--   After Corollary8: common fixed state
-- statement:
--   For every nonempty finite-capacity set $A$, its closed convex hull contains a state fixed by every capacity-preserving CPTP map carrying $A$ into that hull:
--
--   $$\exists\omega\in\overline{\operatorname{co}}A\quad\forall\Phi\in F(A),\ \Phi(\omega)=\omega.$$
--
--   No commutation assumption on the channels is required.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 35, After Corollary8: common fixed state

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

/-- After Corollary8: common fixed state, arXiv:quant-ph/0510073v2, PDF pp.35.
 -/
theorem common_invariant_state_exists {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hfinite : setChiCapacity A < ⊤) :
    ∃ rho ∈ stateClosedConvexHull A, CommonChannelInvariant (PreservingChannels A) rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
