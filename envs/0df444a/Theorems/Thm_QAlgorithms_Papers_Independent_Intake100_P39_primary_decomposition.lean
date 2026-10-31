-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_primary_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.primary_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:04:29.023127+00:00
-- url     : https://prove2.me/theorems/d58651d2-9065-4ddd-b400-68acffef76b8
-- title:
--   Unnumbered primary decomposition, equations (7)–(8)
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   The space $V$ is the symplectically orthogonal internal direct sum of the $A$-invariant nondegenerate real spaces indexed by the distinct eigenvalue orbits:
--   $$V=\bigoplus_{[\lambda]}V_{[\lambda]},\qquad (V_{[\lambda]})_{\mathbb C}=\bigoplus_{\mu\in[\lambda]}E_\mu.$$
--   At $\lambda=\pm1$ there is one complex summand; at a nonreal unit eigenvalue there are two. The zero-dimensional space has the empty direct sum.
--
--
--   This constructs the primary subspaces used by every later normal form.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 7, Unnumbered primary decomposition, equations (7)–(8)

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

/-- PDF pp.7–8, (7)–(8): real, symplectic, invariant primary spaces and their
orthogonal internal direct sum; repeated eigenvalues in an orbit are counted once. -/
theorem primary_decomposition {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    PrimaryDecomposition A := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
