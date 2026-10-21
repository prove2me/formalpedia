-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_freeSymplectic_dense
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.freeSymplectic_dense
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:39:00.339135+00:00
-- url     : https://prove2.me/theorems/9f5c7581-2e10-4b9d-bb11-e9646a06f696
-- title:
--   Free symplectic automorphisms are dense
-- statement:
--   Let $n\ge1$ and give $\operatorname{Sp}(\mathbb R^{2n})$ its usual matrix topology. A matrix $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}$ is free when its upper-right block $B$ is invertible, equivalently $SX^*\cap X^*=\{0\}$ for the momentum plane $X^*$. Then
--
--   $$\overline{\{S\in\operatorname{Sp}(\mathbb R^{2n}):\det B\ne0\}}=\operatorname{Sp}(\mathbb R^{2n}).$$
--
--   Freeness is the domain of quadratic generating functions; it does not exclude fixed points.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 17, Unnumbered: density of free symplectic automorphisms

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF p.17, §3.3: free symplectic automorphisms are dense. Freeness means
invertibility of the upper-right B block, not det(S-I) nonzero. -/
theorem freeSymplectic_dense (n : ℕ) (hn : 0 < n) :
    Dense {S : Matrix.symplecticGroup (Fin n) ℝ |
      ((S : Matrix (Phase n) (Phase n) ℝ).submatrix Sum.inl Sum.inr).det ≠ 0} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
