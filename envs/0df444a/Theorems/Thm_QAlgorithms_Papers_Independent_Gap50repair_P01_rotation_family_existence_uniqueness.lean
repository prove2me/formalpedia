-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_rotation_family_existence_uniqueness
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_family_existence_uniqueness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:30:10.944287+00:00
-- url     : https://prove2.me/theorems/a27547b6-f6f8-4a32-9ce0-f35a2654444e
-- title:
--   Theorem 10
-- statement:
--   For every integer $n\ge1$, let $\operatorname{Sp}(2n,\mathbb R)$ use the standard grouped coordinates and symplectic form $\Omega_0$. There is a unique dimension family of continuous circle-valued rotation maps $\rho_n$. It is the spectral family constructed in the paper, and satisfies
--
--   $$
--   \rho_n(A)=\det_{\mathbb C}A\ (A\in U(n)),\quad
--   \rho_n(KAK^{-1})=\rho_n(A),\quad
--   \rho_{n+m}(A\oplus B)=\rho_n(A)\rho_m(B).
--   $$
--
--   Here $A,K$ are symplectic, $B\in\operatorname{Sp}(2m,\mathbb R)$, $m\ge1$, and $\oplus$ is the symplectic direct sum in grouped coordinates. If $A$ has no eigenvalue on the unit circle, then $\rho_n(A)\in\{1,-1\}$. Uniqueness compares all such families on every symplectic matrix in every positive dimension. No semisimplicity or endpoint assumption is imposed. This identifies the rotation family used to construct the index.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 8, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Theorem 10 ([12]), PDF p.8: existence and uniqueness of the complete
continuous dimension family, including the direct-sum axiom. -/
theorem rotation_family_existence_uniqueness :
    RotationFamilyAxioms (fun _ A => spectralRotation A) ∧
    (∀ r, RotationFamilyAxioms r → ∀ n, 1 ≤ n →
      ∀ A : GroupedRealMatrix n, IsSymplectic A → r n A = spectralRotation A) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
