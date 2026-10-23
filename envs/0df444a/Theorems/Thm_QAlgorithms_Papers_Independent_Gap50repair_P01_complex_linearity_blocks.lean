-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_complex_linearity_blocks
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.complex_linearity_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:13:40.388994+00:00
-- url     : https://prove2.me/theorems/d2949150-325b-4b78-9833-4f88ab6cf819
-- title:
--   Lemma 3
-- statement:
--   Let $F,B,C,D$ be real $n\times n$ matrices and put $A=\left(\begin{smallmatrix}F&B\\C&D\end{smallmatrix}\right)$. Identify $(x,y)\in\mathbb R^{2n}$ with $z=x+iy\in\mathbb C^n$, using the standard complex structure $J_0$. Then
--
--   $$AJ_0=J_0A\quad\Longleftrightarrow\quad D=F\ \text{and}\ C=-B.$$
--
--   Under these equivalent conditions, the complex action is $\widetilde A(x+iy)=Fx+By+i(Cx+Dy)=(F+iC)(x+iy)$. The statement fixes the source's real-to-complex block convention, including the signs.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 5, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 3, PDF p.5: block criterion and the complete complex action. -/
theorem complex_linearity_blocks {n : ℕ} (F B C D : Matrix (Fin n) (Fin n) ℝ) :
    (CommutesWithComplexStructure (Matrix.fromBlocks F B C D) ↔ D = F ∧ C = -B) ∧
    (D = F → C = -B → ∀ x y : Fin n → ℝ,
      (fun i => (((Matrix.fromBlocks F B C D).mulVec (Sum.elim x y)) (Sum.inl i) : ℂ) +
        Complex.I*(((Matrix.fromBlocks F B C D).mulVec (Sum.elim x y)) (Sum.inr i) : ℂ)) =
      (complexActionMatrix (Matrix.fromBlocks F B C D)).mulVec (fun i => (x i : ℂ)+Complex.I*(y i : ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
