-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_real_kernel_form_symmetric
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.real_kernel_form_symmetric
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:09:54.259987+00:00
-- url     : https://prove2.me/theorems/83b134ab-539f-4ef6-88a4-c605bee14e1e
-- title:
--   Definition 11 — real kernel form and symmetry
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   For every $a\in\{1,-1\}$, $k\ge1$, and $v,w\in\ker(A-aI)^{2k}$,
--   $$Q^a_{2k}(v,w)=Q^a_{2k}(w,v).$$
--   No symmetry is asserted outside that kernel.
--
--
--   This verifies the symmetry claim accompanying Definition 11.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 17, Definition 11 — real kernel form and symmetry

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

/-- PDF p.17, Definition 11: symmetry on the STATED kernel, not on the ambient space. -/
theorem real_kernel_form_symmetric {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (a : ℝ) (ha : a = 1 ∨ a = -1) (k : ℕ) (hk : 0 < k)
    (v w : RVec n) (hv : (realShift A a ^ (2 * k)) v = 0)
    (hw : (realShift A a ^ (2 * k)) w = 0) :
    realQ A a k v w = realQ A a k w v := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
