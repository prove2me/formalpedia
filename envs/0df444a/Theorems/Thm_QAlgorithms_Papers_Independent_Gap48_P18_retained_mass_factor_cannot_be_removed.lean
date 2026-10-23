-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_retained_mass_factor_cannot_be_removed
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.retained_mass_factor_cannot_be_removed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T08:00:40.595165+00:00
-- url     : https://prove2.me/theorems/e5437b7c-2f06-463b-9ef7-b22d2ec2b5cf
-- title:
--   Remark 11
-- statement:
--   There is a nonempty set $A$ of states on a separable infinite-dimensional Hilbert space, of finite capacity, and an orthogonal projection $P$ with positive uniform retained mass such that
--
--   $$\bar C(\Theta_P(A))>\bar C(A).$$
--
--   Thus the coefficient $\eta(A,P)$ in Lemma 12 cannot be replaced by one. Remark 12 supplies a concrete family witnessing this phenomenon.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 73, Remark 11

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

/-- Remark 11, arXiv:quant-ph/0510073v2, PDF pp.73.
 -/
theorem retained_mass_factor_cannot_be_removed :
    ∃ (A : Set (State ℕ)) (P : BoundedOrthogonalProjection ℕ), A.Nonempty ∧
      setChiCapacity A < ⊤ ∧ 0 < projectionSuccessInfimum P A ∧
      setChiCapacity A < setChiCapacity (projectionImage P A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
