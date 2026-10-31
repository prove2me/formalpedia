-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_triangular_symplectic_criterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.triangular_symplectic_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:06:27.616371+00:00
-- url     : https://prove2.me/theorems/cd27b827-2be3-416c-a256-39dca3bc4424
-- title:
--   Unnumbered triangular symplectic criterion, equation (18)
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   Let $B,C,D$ be real $n\times n$ matrices. Then
--   $$\begin{pmatrix}B&C\\0&D\end{pmatrix}\in\operatorname{Sp}(2n,\mathbb R)\quad\Longleftrightarrow\quad D\text{ is invertible},\ B=(D^T)^{-1},\ C=(D^T)^{-1}S\text{ for a symmetric }S.$$
--   Invertibility on the right records the domain of the ordinary inverse used in the source, including the empty-matrix case $n=0$.
--
--
--   This is the exact block-triangular symplectic criterion.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 11, Unnumbered triangular symplectic criterion, equation (18)

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

/-- PDF p.11, (18): inverse-domain convention is explicit on the RHS.
In particular the zero D in positive dimension cannot satisfy the RHS. -/
theorem triangular_symplectic_criterion {n : ℕ}
    (B C D : Matrix (Fin n) (Fin n) ℝ) :
    IsSymplectic (Matrix.fromBlocks B C 0 D) ↔
      IsUnit D.det ∧ B = D.transpose⁻¹ ∧
        ∃ S : Matrix (Fin n) (Fin n) ℝ, S.transpose = S ∧ C = D.transpose⁻¹ * S := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
