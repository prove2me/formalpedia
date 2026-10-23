-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_simple_semisimple_dense
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.simple_semisimple_dense
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:20:58.882615+00:00
-- url     : https://prove2.me/theorems/59e4deef-e1df-4b37-918d-f5c1cb6bb45a
-- title:
--   Proposition 26
-- statement:
--   Let $A\in\operatorname{Sp}(2n,\mathbb R)$. For every $\varepsilon>0$ there is a real symplectic matrix $B$ such that
--
--   $$\|B-A\|_{\rm F}<\varepsilon,$$
--
--   and $B$ has distinct complex eigenvalues and is diagonalizable over $\mathbb C$. Explicitly, some invertible complex matrix $P$ conjugates $B$ to a diagonal matrix. Frobenius distance gives the ordinary finite-dimensional topology, so this is the stated density of semisimple symplectic matrices with distinct eigenvalues. No eigenvalue multiplicity condition has been dropped.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 30, Proposition 26

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 26, PDF pp.30–31; 'distinct eigenvalues' and diagonalization are retained. -/
theorem simple_semisimple_dense {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    ∀ eps : ℝ, 0 < eps → ∃ B : GroupedRealMatrix n,
      IsSymplectic B ∧ dist B A < eps ∧ (complexify B).charpoly.roots.Nodup ∧
      ∃ P : CMat n, ∃ d : Coord n → ℂ,
        P.det ≠ 0 ∧ P⁻¹*complexify B*P = Matrix.diagonal d := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
