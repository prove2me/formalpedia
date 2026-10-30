-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_commuting_pure_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.commuting_pure_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:34:35.240519+00:00
-- url     : https://prove2.me/theorems/120bf1cf-467d-4e14-8668-3dd10a29722d
-- title:
--   Abstract and introduction: commuting observables make individual measurements sufficient
-- statement:
--   Let $d,n\ge1$ and let the commutative unital adjoint-closed algebra $\mathcal A$ define an identity-channel estimation problem with invariant pure-state prior and invariant measurable parameter vector. There is a joint spectral measurement of generators of $\mathcal A$, fixed before the original POVM is chosen, such that every normalized POVM has a simulator obtained by applying this measurement separately to the copies and stochastically processing its outcomes. For all positive-probability parameter boxes,
--   $$q_M(B\mid s\in\Delta)=q_{M'}(B\mid s\in\Delta).$$
--   Consequently every figure of merit depending on these laws has the same attainable values using individual measurements.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 1, Abstract and introduction: commuting observables make individual measurements sufficient

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

/-- PDF pp.1,3-4,21-22: when the commutative algebra defines the prior
and all relevant parameters, individual measurements suffice for pure priors. -/
theorem commuting_pure_estimation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y = Y * X)
    (p : EstimationPrior I l) (hsym : Symmetry p (unitaryCentralizer (A : Set (Mat I)))) (hpure : PurePrior p) :
    ∃ E : GeneratorSpectralPVM A, ∀ M : Measurements.OperatorPOVM (Fin n → I) O,
      ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
        (∃ K : (Fin n → Fin E.count) → Measure O, Postprocess E K N.operator) ∧
        EquallyInformative p (piKron n) M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
