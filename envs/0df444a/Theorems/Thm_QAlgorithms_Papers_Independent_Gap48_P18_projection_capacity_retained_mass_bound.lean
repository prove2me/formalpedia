-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_projection_capacity_retained_mass_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.projection_capacity_retained_mass_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:58:56.844984+00:00
-- url     : https://prove2.me/theorems/4bb9bd03-2a12-4557-b7fa-81fb6d9569e8
-- title:
--   Lemma 12
-- statement:
--   Let $A$ be nonempty with finite capacity, let $P$ be an orthogonal projection, and suppose $\eta(A,P)=\inf_{\rho\in A}\operatorname{Tr}P\rho>0$. Then
--
--   $$\eta(A,P)\,\bar C(\Theta_P(A))\le\bar C(A).$$
--
--   The retained-mass factor is essential; the positive infimum also ensures that every input in $A$ can be normalized.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 72, Lemma 12

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

/-- Lemma 12, arXiv:quant-ph/0510073v2, PDF pp.72.
 -/
theorem projection_capacity_retained_mass_bound {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hfinite : setChiCapacity A < ⊤)
    (P : BoundedOrthogonalProjection I) (heta : 0 < projectionSuccessInfimum P A) :
    projectionSuccessInfimum P A * setChiCapacity (projectionImage P A) ≤ setChiCapacity A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
