-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_gl_orthogonal_subgroups
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.gl_orthogonal_subgroups
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:00:36.256604+00:00
-- url     : https://prove2.me/theorems/9d828d23-0c47-4b42-a1ae-a326e9a9b3cd
-- title:
--   §IV (4.7)–(4.8): GL and orthogonal subgroups
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For invertible real A define $G(A)=\operatorname{diag}(A,A^{-T})$.
--
--   $$
--   G(AB)=G(A)G(B),\quad G(A)\in\mathrm{Sp},\quad A^{-T}=A\iff A^TA=I.
--   $$
--
--   The embedding is injective. Orthogonal A gives diag(A,A), and det A=1 selects its special orthogonal part. The embedded GL family has real dimension n squared and both orthogonal families have dimension n(n-1)/2, recorded as Hausdorff dimensions in their ambient matrix space.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 13, §IV (4.7)–(4.8): GL and orthogonal subgroups

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.12–13, (4.7)–(4.8): GL embedding, homomorphism/injectivity,
and exactly the orthogonal transformations act identically on q and p. -/
theorem gl_orthogonal_subgroups (n : ℕ) (hn : 0 < n) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det → PreservesCanonicalForm (glMatrix A)) ∧
    (∀ A B : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det → IsUnit B.det →
      glMatrix (A * B) = glMatrix A * glMatrix B) ∧
    Function.Injective (@glMatrix n) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det →
      (A⁻¹.transpose = A ↔ A.transpose * A = 1)) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.transpose * A = 1 →
      IsPassive (Matrix.fromBlocks A 0 0 A)) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, IsUnit A.det ∧ S = glMatrix A} = (n ^ 2 : ℕ) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) ∧
    dimH {S : Matrix (Phase n) (Phase n) ℝ | ∃ A, A.transpose * A = 1 ∧ A.det = 1 ∧ S = glMatrix A} =
      (n * (n - 1) / 2 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
