-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_rotation_powers_not_homomorphism
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_powers_not_homomorphism
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:19:03.919983+00:00
-- url     : https://prove2.me/theorems/4efc5bd9-fb08-4e91-88e0-de77f4e44cd8
-- title:
--   Proposition 19
-- statement:
--   Let $n\ge1$ and let $\rho$ be the spectral rotation map of (18). This map is not a group homomorphism: there exist symplectic matrices $A,B$ such that $\rho(AB)\ne\rho(A)\rho(B)$. Nevertheless,
--
--   $$\rho(A^N)=\rho(A)^N\qquad\text{for every }A\in\operatorname{Sp}(2n,\mathbb R),\ N\in\mathbb Z.$$
--
--   Integer powers include $N=0$ and negative powers formed using the inverse. This retains both clauses and distinguishes power compatibility from multiplicativity on unrelated matrices.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 15, Proposition 19

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 19, PDF p.15: failure of multiplicativity and all integer powers. -/
theorem rotation_powers_not_homomorphism {n : ℕ} (hn : 1 ≤ n) :
    (∃ A B : GroupedRealMatrix n, IsSymplectic A ∧ IsSymplectic B ∧ spectralRotation (A*B) ≠ spectralRotation A*spectralRotation B) ∧
    (∀ A : GroupedRealMatrix n, IsSymplectic A → ∀ k : ℤ, spectralRotation (integerPower A k) = spectralRotation A^k) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
