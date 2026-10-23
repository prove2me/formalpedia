-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_generalized_eigenspaces_orthogonal
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_eigenspaces_orthogonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:18:37.700346+00:00
-- url     : https://prove2.me/theorems/d2b76423-7220-4e4c-8ed7-bcdcb4b04edb
-- title:
--   Corollary 15
-- statement:
--   Let $A$ be a real symplectic matrix, complexified to $\mathbb C^{2n}$, and let $\lambda,\mu$ be eigenvalues with $\lambda\mu\ne1$. Write $E_\lambda=\bigcup_{j>0}\ker(A-\lambda I)^j$ for the full generalized eigenspace. Then
--
--   $$\Omega_{0,\mathbb C}(v,w)=0\qquad(v\in E_\lambda,\ w\in E_\mu).$$
--
--   The complex symplectic form is bilinear. The result concerns generalized eigenvectors of arbitrary height, not only ordinary eigenvectors, and supplies the source's orthogonal spectral decomposition.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 14, Corollary 15

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Corollary 15, PDF p.14: full generalized eigenspaces. -/
theorem generalized_eigenspaces_orthogonal {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z u : ℂ) (hz : IsEigenvalue A z)
    (hu : IsEigenvalue A u) (hzu : z*u ≠ 1) :
    ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A u, omegaC v w = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
