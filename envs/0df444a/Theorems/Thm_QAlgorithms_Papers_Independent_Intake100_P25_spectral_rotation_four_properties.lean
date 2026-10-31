-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_spectral_rotation_four_properties
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.spectral_rotation_four_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:20:34.465323+00:00
-- url     : https://prove2.me/theorems/ac35a749-bfb4-49b5-9bed-28daa3c73772
-- title:
--   Proposition 6 [SZ92, AD10]: four rotation properties
-- statement:
--   Let $\rho$ be the spectral rotation of Definition 5 on each finite-dimensional real symplectic group, with the real Krein form $\operatorname{Im}\Omega_0(z,\overline{z'})$ and its positive inertia. It has the following four properties:
--
--   1. $\rho(A)=\det_{\mathbb C}A$ for every orthogonal symplectic matrix $A$.
--   2. $\rho(KAK^{-1})=\rho(A)$ for every pair of symplectic matrices $A,K$ of the same dimension.
--   3. $\rho(A)\in\{1,-1\}$ whenever $A$ has no eigenvalue on the unit circle.
--   4. For symplectic matrices $A,B$ on two factors, with grouped symplectic direct sum $\diamond$,
--
--   $$\rho(A\diamond B)=\rho(A)\rho(B).$$
--
--   The map is the specified spectral rotation; no uniqueness assertion is included. Empty symplectic factors have determinant and spectral product equal to $1$. These properties describe its behavior under the basic symplectic operations.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 5, Proposition 6 [SZ92, AD10]

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Proposition 6 [SZ92,AD10], PDF pp.5-6: precisely the four rotation properties.
The spectral map is fixed by Definition 5; uniqueness is not asserted. -/
theorem spectral_rotation_four_properties :
    (∀ n, ∀ A : GroupedRealMatrix n, IsSymplectic A → IsOrthogonal A →
      spectralRotation A = complexActionDet A) ∧
    (∀ n, ∀ A K : GroupedRealMatrix n, IsSymplectic A → IsSymplectic K →
      spectralRotation (K*A*K⁻¹) = spectralRotation A) ∧
    (∀ n, ∀ A : GroupedRealMatrix n, IsSymplectic A →
      (∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) → spectralRotation A = 1 ∨ spectralRotation A = -1) ∧
    (∀ n m, ∀ A : GroupedRealMatrix n, ∀ B : GroupedRealMatrix m,
      IsSymplectic A → IsSymplectic B →
      spectralRotation (symplecticSum A B) = spectralRotation A*spectralRotation B) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
