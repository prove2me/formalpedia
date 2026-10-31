-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_circle_sign_counts
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_circle_sign_counts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:14:23.365664+00:00
-- url     : https://prove2.me/theorems/8ace0017-a0ba-45cf-accc-02e7557beae9
-- title:
--   Proposition 17 — nonreal unit-circle sign counts
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   For any valid unit-circle normal decomposition with chain lengths $m_j\ge1$ and signs $s_j\in\{1,-1\}$, and for every $m\ge1$,
--   $$n_+(Q^\lambda_m)=\#\{j:m_j=m,s_j=1\},\qquad n_-(Q^\lambda_m)=\#\{j:m_j=m,s_j=-1\}.$$
--   The corresponding real block dimension is $2m$ in both families.
--
--
--   This determines both sign counts using complex Hermitian inertia, for any valid decomposition.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 26, Proposition 17 — nonreal unit-circle sign counts

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

/-- PDF p.26, Proposition 17: BOTH signs for ANY valid decomposition;
inertia uses complex dimensions, avoiding the doubled underlying-real count. -/
theorem unit_circle_sign_counts {n L : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hplus : z ≠ 1) (hminus : z ≠ -1)
    (m : Fin L → ℕ) (s : Fin L → ℤ) (hNF : UnitNormal A z m s) :
    UnitSignCounts A z m s := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
