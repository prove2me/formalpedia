-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_unitary_orthogonal_symplectic
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.unitary_orthogonal_symplectic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:14:19.041177+00:00
-- url     : https://prove2.me/theorems/b4ca09be-4398-4772-900d-368a564713e2
-- title:
--   Proposition 5
-- statement:
--   Identify $\mathbb R^{2n}$ with $\mathbb C^n$ by $(x,y)\mapsto x+iy$, and use $\Omega_0=\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. For a real linear transformation $A$, complex unitary membership means that $A$ is complex linear and its complex matrix preserves the standard Hermitian product. Then
--
--   $$U(n)=O(2n,\mathbb R)\cap\operatorname{Sp}(2n,\mathbb R).$$
--
--   Both directions are asserted, with unitary membership defined independently of the intersection. This identifies the compact subgroup used by the degree constructions.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 5, Proposition 5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 5, PDF p.5: independently defined unitary membership. -/
theorem unitary_orthogonal_symplectic {n : ℕ} (A : GroupedRealMatrix n) :
    IsUnitaryReal A ↔ IsOrthogonal A ∧ IsSymplectic A := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
