-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_rotation_generalized_spectral_formula
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_generalized_spectral_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:30:58.392987+00:00
-- url     : https://prove2.me/theorems/86ab46a0-6b21-419e-b97d-4a0c5274bc3f
-- title:
--   Theorem 16
-- statement:
--   Let $n\ge1$ and $A\in\operatorname{Sp}(2n,\mathbb R)$. Let $E_\lambda$ be its full complex generalized eigenspace. For every eigenvalue $\lambda$ on the unit circle other than $\pm1$, the real bilinear form
--
--   $$Q_\lambda(v,w)=\operatorname{Im}\Omega_0(v,\overline w),\qquad v,w\in E_\lambda,$$
--
--   is symmetric and nondegenerate on the underlying real space. Its positive inertia $m^+(\lambda)$ is even. Write $m^-=\sum_{\lambda\in\mathbb R,\,\lambda<0}\dim_{\mathbb C}E_\lambda$; this integer is also even. The spectral rotation map satisfies
--
--   $$\rho(A)=(-1)^{m^-/2}\prod_{\substack{\lambda\in\sigma(A)\cap S^1\\\lambda\ne\pm1}}\lambda^{m^+(\lambda)/2}.$$
--
--   The product ranges over distinct eigenvalues, with their contributions weighted by these multiplicities. All powers have integer exponents. This formula determines the rotation contribution of each spectral component without choosing fractional-power branches.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 14, Theorem 16

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Theorem 16 ([12,3]), PDF pp.14–15: real symmetric nondegenerate Krein
forms on the full generalized eigenspaces and formula (18). The half exponents
are integers; no fractional complex power is used. -/
theorem rotation_generalized_spectral_formula {n : ℕ} (hn : 1 ≤ n)
    (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    (∀ z ∈ eigenvalues A, ‖z‖ = 1 → z ≠ 1 → z ≠ -1 →
      (∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A z,
        kreinPairing v w = kreinPairing w v) ∧
      (∀ v ∈ generalizedSpace A z,
        (∀ w ∈ generalizedSpace A z, kreinPairing v w = 0) → v = 0) ∧
      2 ∣ kreinPositive A z) ∧
    (2 ∣ ∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ z.re < 0),
      Module.finrank ℂ (generalizedSpace A z)) ∧
    spectralRotation A =
      (-1 : ℂ)^((∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ z.re < 0),
        Module.finrank ℂ (generalizedSpace A z))/2) *
      ∏ z ∈ (eigenvalues A).filter (fun z => ‖z‖ = 1 ∧ z ≠ 1 ∧ z ≠ -1),
        z^(kreinPositive A z/2) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
