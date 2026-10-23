-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_positive_eigenvalue_component
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.positive_eigenvalue_component
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:22:05.922593+00:00
-- url     : https://prove2.me/theorems/32e64ed8-ee57-41fc-9301-2542f5aac15e
-- title:
--   Remark 31
-- statement:
--   Let $A\in\operatorname{Sp}(2n,\mathbb R)$ with $\det(A-I)\ne0$. Let $m_+(A)$ be the total algebraic multiplicity of its real positive eigenvalues; repeated roots are counted repeatedly. Then
--
--   $$\det(A-I)>0\quad\Longleftrightarrow\quad 4\mid m_+(A).$$
--
--   This identifies the positive component using the spectrum. Counting distinct spectral values instead of algebraic multiplicities would give a different statement.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 34, Remark 31

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 31, PDF p.34: real positive eigenvalues counted with multiplicity. -/
theorem positive_eigenvalue_component {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (hend : (A-1).det ≠ 0) :
    0 < (A-1).det ↔ 4 ∣ ∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ 0 < z.re),
      algebraicMultiplicity A z := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
