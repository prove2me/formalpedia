-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_generalized_kernel_orthogonal_range
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_kernel_orthogonal_range
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:17:53.157987+00:00
-- url     : https://prove2.me/theorems/3678af00-4bef-409d-ae19-6dfcc564a808
-- title:
--   Lemma 14
-- statement:
--   Let $A$ be a real symplectic matrix and let $\lambda$ be a complex eigenvalue. Extend $A$ and $\Omega_0$ complex linearly. For every integer $j\ge0$,
--
--   $$\ker(A-\lambda I)^j=\bigl(\operatorname{im}(A-\lambda^{-1}I)^j\bigr)^{\perp_{\Omega_0}}.$$
--
--   The orthogonal complement is for the complex bilinear symplectic form, with no conjugation. Symplecticity implies $\lambda\ne0$. At $j=0$, the kernel is zero and the image is the whole complexified space. This is the annihilator identity behind the quotient pairings.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 13, Lemma 14

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 14, PDF pp.13–14; complex bilinear orthogonal, no conjugation. -/
theorem generalized_kernel_orthogonal_range {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : IsEigenvalue A z) (j : ℕ) :
    ∀ v : Coord n → ℂ, (shifted A z^j) v = 0 ↔
      ∀ w ∈ LinearMap.range (shifted A z⁻¹^j), omegaC v w = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
