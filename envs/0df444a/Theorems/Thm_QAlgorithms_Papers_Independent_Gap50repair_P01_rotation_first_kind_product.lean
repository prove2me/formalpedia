-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_rotation_first_kind_product
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_first_kind_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:31:25.215426+00:00
-- url     : https://prove2.me/theorems/cb1d5f73-0e04-451d-a003-63eec0668256
-- title:
--   Remark 18
-- statement:
--   Let $n\ge1$ and $A\in\operatorname{Sp}(2n,\mathbb R)$, and let $E_\lambda$ denote its complex generalized eigenspace. The multiplicity $r(\lambda)$ of an eigenvalue of the first kind is its algebraic multiplicity if $|\lambda|<1$; it is $\frac12\dim_{\mathbb C}E_\lambda$ at $\lambda=\pm1$; and it is half the real positive inertia of $\operatorname{Im}\Omega_0(v,\overline w)$ on $E_\lambda$ for other $|\lambda|=1$. It is zero when $|\lambda|>1$. Then every eigenvalue is nonzero and
--
--   $$\sum_{\lambda\in\sigma(A)}r(\lambda)=n,\qquad
--   \rho(A)=\prod_{\lambda\in\sigma(A)}\left(\frac{\lambda}{|\lambda|}\right)^{r(\lambda)}.$$
--
--   Thus repeated eigenvalues retain their prescribed multiplicity, including the half-multiplicity convention of Definition 17. This gives the first-kind expression for the same rotation map.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 15, Remark 18

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 18 ([12]), PDF p.15, with Definition 17: spectral product (19)
with multiplicities and nonzero denominators. There are n first-kind entries. -/
theorem rotation_first_kind_product {n : ℕ} (hn : 1 ≤ n)
    (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    (∀ z ∈ eigenvalues A, z ≠ 0) ∧
    (∑ z ∈ eigenvalues A, firstKindMultiplicity A z) = n ∧
    spectralRotation A = ∏ z ∈ eigenvalues A,
      (z/(‖z‖ : ℂ))^(firstKindMultiplicity A z) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
