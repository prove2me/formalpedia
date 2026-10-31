-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_kernel_form_hermitian
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_kernel_form_hermitian
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:13:50.2406+00:00
-- url     : https://prove2.me/theorems/1377ea38-0174-497f-ae72-d6477e2c4958
-- title:
--   Definition 16 — Hermitian kernel forms
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   For every positive integer $m$ and $v,w\in\ker N_\lambda^m$,
--   $$Q^\lambda_m(v,w)=\overline{Q^\lambda_m(w,v)}.$$
--   For $m=1$ this is $i\Omega_{\mathbb C}(v,\bar w)$. No Hermitian assertion is made on the unrestricted ambient space.
--
--
--   This supplies the substantive Hermitian claim attached to Definition 16.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 26, Definition 16 — Hermitian kernel forms

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

/-- PDF p.26, Definition 16: the kernel form is Hermitian (linear first,
conjugate-linear second); the m=1 case has k=0 and coefficient i. -/
theorem unit_kernel_form_hermitian {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hplus : z ≠ 1) (hminus : z ≠ -1)
    (m : ℕ) (hm : 0 < m) (v w : CVec n)
    (hv : (shifted A z ^ m) v = 0) (hw : (shifted A z ^ m) w = 0) :
    unitQ A z m v w = star (unitQ A z m w v) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
