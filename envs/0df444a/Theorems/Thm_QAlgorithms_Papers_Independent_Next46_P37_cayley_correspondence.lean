-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P37_cayley_correspondence
-- name    : QAlgorithms.Papers.Independent.Next46.P37.cayley_correspondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:39:06.930833+00:00
-- url     : https://prove2.me/theorems/3052138a-b57f-4eea-9c43-832e7c8e3f25
-- title:
--   Symplectic Cayley transform and its inverse
-- statement:
--   Let $n\ge1$ and use grouped position and momentum coordinates on $\mathbb R^{2n}$, with $J=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$. For a real matrix $S$ with $\det(S-I)\ne0$ define $M_S=\tfrac12J(S+I)(S-I)^{-1}$. For a real matrix $M$ with $\det(M-\tfrac12J)\ne0$ define $C(M)=(M-\tfrac12J)^{-1}(M+\tfrac12J)$.
--
--   For every symplectic $S$ with $\det(S-I)\ne0$, and every real $M$ with $\det(M-\tfrac12J)\ne0$, respectively, one has
--
--   $$
--   M_S=M_S^T,\qquad \det(M_S-\tfrac12J)\ne0,\qquad C(M_S)=S,
--   $$
--   $$
--   \det(C(M)-I)\ne0,\qquad M_{C(M)}=M,\qquad C(M)\in\operatorname{Sp}(n)\ \Longleftrightarrow\ M=M^T.
--   $$
--
--   This is the inverse correspondence between nonfixed symplectic matrices and the stated domain of symmetric real matrices.
-- source:
--   On the Weyl Representation of Metaplectic Operators, arXiv:math/0503708v1, PDF p. 6, §3.1, unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Next46.P37

/-- PDF p.6, §3.1, unnumbered Cayley-transform result: symmetry and the
inverse correspondence, with both inverse domains explicit. The matrix is real
by type; no operator or integration assumptions enter this algebraic result. -/
theorem cayley_correspondence (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (cayley S).IsSymm ∧
      (cayley S - (1 / 2 : ℝ) • sigma n).det ≠ 0 ∧
      inverseCayley (cayley S) = S) ∧
    (∀ M : Matrix (Phase n) (Phase n) ℝ,
      (M - (1 / 2 : ℝ) • sigma n).det ≠ 0 →
      (inverseCayley M - 1).det ≠ 0 ∧
      cayley (inverseCayley M) = M ∧
      (inverseCayley M ∈ Matrix.symplecticGroup (Fin n) ℝ ↔ M.IsSymm)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P37

end
