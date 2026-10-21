-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_freeSymplectic_determinant
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.freeSymplectic_determinant
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:39:38.707982+00:00
-- url     : https://prove2.me/theorems/c53c192b-8876-4386-ac73-a3ffc639dbbf
-- title:
--   Determinant identity for a free symplectic matrix
-- statement:
--   Let $n\ge1$ and $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}\in\operatorname{Sp}(\mathbb R^{2n})$ with $\det B\ne0$. Set $P=DB^{-1}$, $L=B^{-1}$ and $Q=B^{-1}A$. Then
--
--   $$\det(S-I)=(-1)^n\det B\,\det\bigl(B^{-1}A+DB^{-1}-B^{-1}-(B^T)^{-1}\bigr)=(-1)^n\det(L^{-1})\det(P+Q-L-L^T).$$
--
--   The identity also applies when either side vanishes. It is the valid determinant clause of Lemma 7; the full lemma's unconditional invertibility continuation is separately deferred.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 17, Lemma 7 (42): determinant identity (valid clause)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF pp.17-18, Lemma 7, (42): both forms of the determinant identity.
This is precisely the valid first clause. The full printed lemma, including
its false unconditional invertibility continuation, is deferred separately. -/
theorem freeSymplectic_determinant (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hB : B.det ≠ 0) :
    let S := Matrix.fromBlocks A B C D
    let P := D * B⁻¹
    let L := B⁻¹
    let Q := B⁻¹ * A
    (S - 1).det = (-1 : ℝ) ^ n * B.det *
      (B⁻¹ * A + D * B⁻¹ - B⁻¹ - (B.transpose)⁻¹).det ∧
    (S - 1).det = (-1 : ℝ) ^ n * (L⁻¹).det * (diagonalHessian P L Q).det := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
