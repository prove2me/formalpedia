-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_generalized_eigenspaces_orthogonal
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.generalized_eigenspaces_orthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:03:55.826136+00:00
-- url     : https://prove2.me/theorems/bd5b1e69-0241-464d-b77b-c212215b2d6d
-- title:
--   Corollary 4 — orthogonality of generalized eigenspaces
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For any $\lambda,\mu\in\mathbb C$ with $\lambda\mu\ne1$,
--   $$\Omega_{\mathbb C}(v,w)=0\qquad(v\in E_\lambda,\ w\in E_\mu).$$
--   Non-eigenvalues are allowed and have zero generalized eigenspace.
--
--
--   This supplies the orthogonality of distinct primary components.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 7, Corollary 4 — orthogonality of generalized eigenspaces

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

/-- PDF p.7, Corollary 4: no artificial eigenvalue hypothesis is needed. -/
theorem generalized_eigenspaces_orthogonal {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z t : ℂ) (hzt : z * t ≠ 1)
    (v w : CVec n) (hv : v ∈ generalizedSpace A z) (hw : w ∈ generalizedSpace A t) :
    omegaC v w = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
