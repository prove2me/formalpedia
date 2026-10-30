-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_distorted_prior_explicit_simulator
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.distorted_prior_explicit_simulator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:33:05.976259+00:00
-- url     : https://prove2.me/theorems/1ae35101-9ccb-43a7-aa00-661d4b9db83c
-- title:
--   Remark 14: explicit simulator for Theorem 13
-- statement:
--   Under Theorem 13’s assumptions, including a specified distortion channel $\mathcal N$, a normalized $\mathcal A^{\otimes n}$-valued simulator is
--   $$M'=L_+\circ(\mathcal N^\dagger)^{\otimes n}\circ\mathcal E^\dagger(M).$$
--   Composition acts from right to left. The adjoints are trace duals of the physical trace-preserving channels, while $L_+$ is the corrected Heisenberg unital completely positive map. This single simulator preserves all positive-probability parameter-conditioned outcome laws in the original experiment.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 21, Remark 14: explicit simulator for Theorem 13

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

/-- PDF p.21, Remark 14: composition is L_plus after (N_dual)^tensor n
after E_dual, using Heisenberg duals of the physical channels. -/
theorem distorted_prior_explicit_simulator [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (p : EstimationPrior I l) (hsym : Symmetry p (unitaryCentralizer (A : Set (Mat I))))
    (E : Mat (Fin n → I) → Mat (Fin n → I)) (hE : IsChannel E)
    (hquiet : Noiseless (tensorAlg n (A : Set (Mat I))) E)
    (N : Mat I → Mat I) (hdist : Distortion (A : Set (Mat I)) p N)
    (M : Measurements.OperatorPOVM (Fin n → I) O) :
    ∃ Mnew : Measurements.OperatorPOVM (Fin n → I) O,
      (∀ B, MeasurableSet B → Mnew.operator B = promotion (A : Set (Mat I)) n false
        (piSuperop (fun _ : Fin n => heisenbergDual N) (heisenbergDual E (M.operator B)))) ∧
      InAlgebra Mnew.operator (tensorAlg n (A : Set (Mat I))) ∧
      EquallyInformative p (E ∘ piKron n) M.operator Mnew.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
