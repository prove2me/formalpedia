-- Prove2me | Theorems.Thm_VectorSpaceOpt_gram_determinant_linear_independence
-- name    : VectorSpaceOpt.gram_determinant_linear_independence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:23:33.989404+00:00
-- url     : https://prove2.me/theorems/157d137f-b54d-49c6-9536-c1b6df8380d3
-- title:
--   Nonvanishing of the Gram determinant is equivalent to linear independence
-- statement:
--   Let $y_1, \dots, y_n$ be vectors in a real inner product space $H$. Their **Gram matrix** is the $n \times n$ matrix of pairwise inner products,
--
--   $$G(y_1, \dots, y_n)_{ij} = \langle y_i,\, y_j \rangle,$$
--
--   and its determinant $g(y_1, \dots, y_n) = \det G$ is the **Gram determinant**. The theorem states that
--
--   $$g(y_1, \dots, y_n) \neq 0 \iff y_1, \dots, y_n \ \text{are linearly independent}.$$
--
--   Equivalently, in contrapositive form: the Gram determinant vanishes exactly when the vectors are linearly dependent. One direction is immediate — a dependency among the vectors induces the same dependency among the rows of $G$. The other direction takes a dependency among the rows, forms the corresponding combination $\sum_i \alpha_i y_i$, and shows it has zero norm.
--
--   This is what makes the normal equations uniquely solvable: the coefficient matrix of that system is the Gram matrix.
--
--   **Formalization Note.** Linear independence is taken of the indexed family, so a family listing the same nonzero vector twice does not count as independent. No completeness or finite-dimensionality is assumed of the ambient space.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.6, Proposition 1, p. 56

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem gram_determinant_linear_independence {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (y : Fin n → H) :
    (Matrix.of fun i j : Fin n => ⟪y i, y j⟫).det ≠ 0 ↔ LinearIndependent ℝ y := by sorry

end VectorSpaceOpt
