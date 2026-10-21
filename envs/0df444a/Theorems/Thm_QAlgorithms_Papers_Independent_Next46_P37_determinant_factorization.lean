-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P37_determinant_factorization
-- name    : QAlgorithms.Papers.Independent.Next46.P37.determinant_factorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:39:40.710625+00:00
-- url     : https://prove2.me/theorems/3c90c726-6bca-49ca-9327-4a8cb07b1d4b
-- title:
--   Determinant factorization for free symplectic matrices
-- statement:
--   Let $n\ge1$ and let $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}\in\operatorname{Sp}(n)$ be real and free, meaning $\det B\ne0$. Define $P=DB^{-1}$, $L=B^{-1}$ and $Q=B^{-1}A$, and put $H=P+Q-L-L^T$. Then both forms of the determinant identity hold:
--
--   $$
--   \det(S-I)=(-1)^n\det B\,\det\!\left(B^{-1}A+DB^{-1}-B^{-1}-(B^T)^{-1}\right)
--   =(-1)^n\det(L^{-1})\,\det H.
--   $$
--
--   The formula relates fixed-point degeneracy of a free symplectic matrix to degeneracy of the Hessian of its generating function restricted to the diagonal. Neither determinant on the two sides is required to be nonzero.
-- source:
--   On the Weyl Representation of Metaplectic Operators, arXiv:math/0503708v1, PDF p. 8, Lemma 4, (19)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Next46.P37

/-- PDF p.8, Lemma 4, equations (19) and (20): both determinant formulas
for an arbitrary free symplectic matrix. P, L and Q in the second formula are
constructed from the blocks as on PDF p.4; det(S-I) may be zero. -/
theorem determinant_factorization (n : ℕ) (hn : 0 < n)
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

end QAlgorithms.Papers.Independent.Next46.P37

end
