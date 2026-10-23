-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_free_lens_subgroups
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.free_lens_subgroups
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:01:33.410221+00:00
-- url     : https://prove2.me/theorems/adf5941c-7f0c-4084-a539-00f43f5cefd0
-- title:
--   §IV (4.15)–(4.17): abelian free/lens subgroups
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $F(B)=\begin{pmatrix}I&B\\0&I\end{pmatrix}$ and $L(C)=\begin{pmatrix}I&0\\C&I\end{pmatrix}$.
--
--   $$
--   F(B)\in\mathrm{Sp}\iff B=B^T,\quad L(C)\in\mathrm{Sp}\iff C=C^T,\quad F(B)F(C)=F(B+C),\quad L(B)L(C)=L(B+C).
--   $$
--
--   Both families are abelian, have dimension n(n+1)/2, and act respectively by (q,p) to (q+Bp,p) and (q,p+Cq). Conjugation by beta sends F(B) to L(-B). These formulas fix the free and lens conventions.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 14, §IV (4.15)–(4.17): abelian free/lens subgroups

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.14–15, (4.15)–(4.17): free/lens membership, additive abelian
composition, canonical actions and dimension n(n+1)/2 (Hausdorff dimension of
their affine linear matrix families, equal to their real Lie dimensions). -/
theorem free_lens_subgroups (n : ℕ) (hn : 0 < n) :
    (∀ B : Matrix (Fin n) (Fin n) ℝ,
      (PreservesCanonicalForm (freeMatrix B) ↔ B.IsSymm) ∧
      (PreservesCanonicalForm (lensMatrix B) ↔ B.IsSymm)) ∧
    (∀ B C : Matrix (Fin n) (Fin n) ℝ,
      freeMatrix B * freeMatrix C = freeMatrix (B + C) ∧
      lensMatrix B * lensMatrix C = lensMatrix (B + C) ∧
      freeMatrix B * freeMatrix C = freeMatrix C * freeMatrix B ∧
      lensMatrix B * lensMatrix C = lensMatrix C * lensMatrix B ∧
      sigma n * freeMatrix B * (sigma n)⁻¹ = lensMatrix (-B)) ∧
    (∀ (B : Matrix (Fin n) (Fin n) ℝ) (z : Phase n → ℝ) (i : Fin n),
      (Matrix.mulVec (freeMatrix B) z) (Sum.inl i) = z (Sum.inl i) + ∑ j, B i j * z (Sum.inr j) ∧
      (Matrix.mulVec (freeMatrix B) z) (Sum.inr i) = z (Sum.inr i) ∧
      (Matrix.mulVec (lensMatrix B) z) (Sum.inl i) = z (Sum.inl i) ∧
      (Matrix.mulVec (lensMatrix B) z) (Sum.inr i) = z (Sum.inr i) + ∑ j, B i j * z (Sum.inl j)) ∧
    dimH {M : Matrix (Phase n) (Phase n) ℝ | ∃ B, B.IsSymm ∧ M = freeMatrix B} =
      (n * (n + 1) / 2 : ℕ) ∧
    dimH {M : Matrix (Phase n) (Phase n) ℝ | ∃ C, C.IsSymm ∧ M = lensMatrix C} =
      (n * (n + 1) / 2 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
