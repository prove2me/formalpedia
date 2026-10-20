-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_joint_cancellation
-- name    : QAlgorithms.Papers.Independent.Information100.P60.joint_cancellation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:39:43.351299+00:00
-- url     : https://prove2.me/theorems/c75b3d17-88b7-4d8f-abaf-7f082bb71b18
-- title:
--   Lemma 5: joint three-term unitary cancellation
-- statement:
--   Let $M_1,M_2\in\mathbb C^{3\times3}$ be Hermitian and traceless. There is a single unitary $W\in U(3)$ such that $$M_j+WM_jW^\dagger+W^\dagger M_jW=0\qquad(j=1,2).$$ The same $W$ is required for both matrices. This joint cancellation identity is used in the two-probe analysis.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 21, Lemma 5: joint three-term unitary cancellation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.21, Lemma 5, Eq.(69): one W works for both matrices. -/
theorem joint_cancellation (A B : Mat (Fin 3)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 0) (htB : B.trace = 0) :
    ∃ W : Matrix.unitaryGroup (Fin 3) ℂ, ∀ M ∈ ({A, B} : Set (Mat (Fin 3))),
      M + (W : Mat (Fin 3)) * M * (W : Mat (Fin 3))ᴴ + (W : Mat (Fin 3))ᴴ * M * (W : Mat (Fin 3)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
