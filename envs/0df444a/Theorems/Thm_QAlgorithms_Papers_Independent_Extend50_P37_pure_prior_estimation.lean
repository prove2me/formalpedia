-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_pure_prior_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.pure_prior_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:30:42.83743+00:00
-- url     : https://prove2.me/theorems/4ad1df0b-ec13-46ac-b02c-a716e592ba93
-- title:
--   Theorem 11: pure-prior multi-copy estimation reduces to the local algebra
-- statement:
--   Let $d,n\ge1$, let $\mathcal A$ be a unital adjoint-closed algebra, and consider the identity-channel $n$-copy experiment. The prior is a probability law supported on density matrices of rank one, and both this law and the measurable finite parameter vector $s$ are invariant under $G_{\mathcal A}$. Every normalized POVM $M$ on an arbitrary measurable outcome space admits one $\mathcal A^{\otimes n}$-valued normalized POVM $M'$ such that
--   $$q_M(B\mid s\in\Delta)=q_{M'}(B\mid s\in\Delta)$$
--   for all measurable outcome events $B$ and measurable parameter boxes $\Delta$ with positive prior probability. These conditionals average over the prior; equality for each individual state is not asserted.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 20, Theorem 11: pure-prior multi-copy estimation reduces to the local algebra

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.20, Theorem 11: equality only after conditioning and averaging
against the invariant pure prior; there is no pointwise-state assertion. -/
theorem pure_prior_estimation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (p : EstimationPrior I l) (hsym : Symmetry p (unitaryCentralizer (A : Set (Mat I))))
    (hpure : PurePrior p) (M : Measurements.OperatorPOVM (Fin n → I) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
      InAlgebra N.operator (tensorAlg n (A : Set (Mat I))) ∧
      EquallyInformative p (piKron n) M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
