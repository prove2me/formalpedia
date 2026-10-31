-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_kernel_image_orthogonals
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.kernel_image_orthogonals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:03:21.112993+00:00
-- url     : https://prove2.me/theorems/723bbea7-6ec6-4cb1-aca1-0ff649ff5f4a
-- title:
--   Lemma 3 — kernel/image symplectic orthogonals
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For every $\lambda\ne0$ and integer $j\ge0$,
--   $$\ker N_\lambda^j=\bigl(\operatorname{im}N_{\lambda^{-1}}^j\bigr)^{\perp_{\Omega_{\mathbb C}}}.$$
--   The orthogonal uses the complex-bilinear form. At $j=0$ both sides are zero.
--
--
--   This identifies the reciprocal shifted kernel and image pairing.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 7, Lemma 3 — kernel/image symplectic orthogonals

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

/-- PDF p.7, Lemma 3. The power j=0 is included. Omega_C is bilinear. -/
theorem kernel_image_orthogonals {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : z ≠ 0) (j : ℕ) (v : CVec n) :
    v ∈ LinearMap.ker (shifted A z ^ j) ↔
      OrthogonalC (LinearMap.range (shifted A z⁻¹ ^ j)) v := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
