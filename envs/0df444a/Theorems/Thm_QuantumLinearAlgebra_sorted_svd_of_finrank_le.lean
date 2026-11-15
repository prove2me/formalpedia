-- Prove2me | Theorems.Thm_QuantumLinearAlgebra_sorted_svd_of_finrank_le
-- name    : QuantumLinearAlgebra.sorted_svd_of_finrank_le
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-15T04:14:20.161002+00:00
-- url     : https://prove2.me/theorems/38854afb-29f1-4f79-bf29-e9b2c9717163
-- title:
--   Sorted rectangular SVD with orthonormal completion of zero singular directions
-- statement:
--   Let $E$ and $F$ be finite-dimensional complex inner product spaces, with $n=\dim E\le m=\dim F$, and let $T:E\to F$ be linear. There are orthonormal bases $(b_i)_{i=0}^{n-1}$ of $E$ and $(c_j)_{j=0}^{m-1}$ of $F$, and real numbers $s_0\ge\cdots\ge s_{n-1}\ge0$, such that
--
--   $$
--   T b_i=s_i c_i\qquad(0\le i<n).
--   $$
--
--   Zero singular values are included; their left vectors are completed to an orthonormal basis of the full codomain. The conclusion also covers zero-dimensional spaces. This is the rectangular singular value decomposition in a form that can be applied directly to maps between projector image subspaces, as needed for Definition 11 of the QSVT paper.
--
--   **Formalization Note.** The index inclusion is `Fin.castLE hnm`; basis vectors and singular values use zero-based indexing. This supporting lemma states the standard linear-map SVD underlying the paper's projected-unitary instance, with the explicit dimension order shown above.
-- source:
--   Supporting standard SVD for Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p.15, Definition 11, Eq.(17), https://arxiv.org/abs/1806.01838v1 . Proof construction adapts the Gram-matrix and orthonormal-completion argument of OAI.GAD.exists_unitary_singular_decomposition, https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ZeroBlockEntropy.lean#L236-L293, to rectangular maps and decreasingly ordered singular values.

import Mathlib.Analysis.InnerProductSpace.SingularValues
set_option autoImplicit false

namespace QuantumLinearAlgebra
theorem sorted_svd_of_finrank_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) (hnm : Module.finrank ℂ E ≤ Module.finrank ℂ F) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (c : OrthonormalBasis (Fin (Module.finrank ℂ F)) ℂ F)
      (s : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
      ∀ i, T (b i) = (s i : ℂ) • c (Fin.castLE hnm i) := by sorry
end QuantumLinearAlgebra
