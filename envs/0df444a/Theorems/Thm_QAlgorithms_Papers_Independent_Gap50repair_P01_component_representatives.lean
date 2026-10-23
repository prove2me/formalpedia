-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_component_representatives
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.component_representatives
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:21:45.484925+00:00
-- url     : https://prove2.me/theorems/d599728f-e74f-4f68-add7-a6b06820b5b8
-- title:
--   Remark 30
-- statement:
--   For $n\ge1$, define $W^+=-I_{2n}$ and $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$ in grouped coordinates. Both matrices are symplectic and
--
--   $$\det(W^+-I)>0,\quad \rho(W^+)=(-1)^n,\qquad \det(W^--I)<0,\quad \rho(W^-)=(-1)^{n-1}.$$
--
--   Thus they are the explicit representatives of the positive and negative components used when extending an admissible path. The first coordinate is available because $n\ge1$.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 32, Remark 30

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 30, PDF p.32: explicit matrices, determinant signs and spectralRotation values. -/
theorem component_representatives {n : ℕ} (hn : 1 ≤ n) :
    IsSymplectic (wPlus n) ∧ 0 < (wPlus n-1).det ∧ spectralRotation (wPlus n) = (-1 : ℂ)^n ∧
    IsSymplectic (wMinus n) ∧ (wMinus n-1).det < 0 ∧ spectralRotation (wMinus n) = (-1 : ℂ)^(n-1) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
