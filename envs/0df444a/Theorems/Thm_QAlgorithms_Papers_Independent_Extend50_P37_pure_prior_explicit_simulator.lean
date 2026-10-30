-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_pure_prior_explicit_simulator
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.pure_prior_explicit_simulator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:31:43.049877+00:00
-- url     : https://prove2.me/theorems/ca6a7c6f-b433-4279-8dcd-877180b07035
-- title:
--   Remark 12: explicit simulator for Theorem 11
-- statement:
--   Under the pure-prior, invariant-parameter, identity-channel assumptions of Theorem 11, the corrected canonical promotion map gives the simulator explicitly:
--   $$M'(B)=L_+(M(B)).$$
--   This is one normalized $\mathcal A^{\otimes n}$-valued POVM preserving every positive-probability parameter-box conditional outcome law. No initial symmetry assumption is placed on $M$.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 20, Remark 12: explicit simulator for Theorem 11

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

/-- PDF p.20, Remark 12 and proof p.27: the corrected canonical L_plus
works even for an initially noninvariant measurement. -/
theorem pure_prior_explicit_simulator [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (p : EstimationPrior I l) (hsym : Symmetry p (unitaryCentralizer (A : Set (Mat I))))
    (hpure : PurePrior p) (M : Measurements.OperatorPOVM (Fin n → I) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
      (∀ B, MeasurableSet B → N.operator B = promotion (A : Set (Mat I)) n false (M.operator B)) ∧
      InAlgebra N.operator (tensorAlg n (A : Set (Mat I))) ∧
      EquallyInformative p (piKron n) M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
