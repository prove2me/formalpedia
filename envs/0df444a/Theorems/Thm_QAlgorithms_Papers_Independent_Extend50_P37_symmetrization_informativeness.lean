-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_symmetrization_informativeness
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.symmetrization_informativeness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:42:28.982549+00:00
-- url     : https://prove2.me/theorems/feea7501-62ea-43e4-a58e-73d664e53c61
-- title:
--   Lemma 16: symmetrization preserves parameter informativeness
-- statement:
--   Consider an identity-channel $n$-copy experiment, $d,n\ge1$, with prior law and finite measurable parameter vector invariant under a unitary subgroup $H$ supplied with normalized Haar probability. For any arbitrary-outcome POVM $M$, its normalized collective twirl
--   $$\widetilde M(B)=\int_H U^{\otimes n}M(B)(U^{\otimes n})^*\,d\mu(U)$$
--   preserves every positive-probability parameter-box conditional outcome law. This is the identity-channel lemma actually used in the source’s proofs.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 25, Lemma 16: symmetrization preserves parameter informativeness

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

/-- PDF pp.25-26, Lemma 16: the identity-channel lemma actually proved.
For a general noncovariant physical channel one must twirl E_dual(M). -/
theorem symmetrization_informativeness [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (H : Set (Mat I)) (mu : Measure (Mat I))
    (hmu : SubgroupHaarProbability H mu) (p : EstimationPrior I l) (hsym : Symmetry p H)
    (M : Measurements.OperatorPOVM (Fin n → I) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
      (∀ B, MeasurableSet B → N.operator B =
        ∫ U, piKron n U * M.operator B * (piKron n U)ᴴ ∂mu) ∧
      EquallyInformative p (piKron n) M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
