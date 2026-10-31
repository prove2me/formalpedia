-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_off_circle_normal_forms
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.off_circle_normal_forms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:07:55.372859+00:00
-- url     : https://prove2.me/theorems/e8bf801e-d712-4873-8e16-e418bee9611b
-- title:
--   Theorem 9 — normal forms off the unit circle
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $z\in\mathbb C$, write $R(z)=\left(\begin{smallmatrix}\Re z&-\Im z\\\Im z&\Re z\end{smallmatrix}\right)$. The real Jordan matrix $J_R(z,2r)$ has $R(z)$ on its $2\times2$ diagonal blocks, $I_2$ on its block superdiagonal, and zeros elsewhere.
--   Fix an eigenvalue $\lambda$ off the unit circle. Set $b=\dim_{\mathbb C}\ker N_\lambda$ and let $q$ be the smallest positive exponent annihilating $E_\lambda$. There are $b$ positive integers $q=q_1\ge\cdots\ge q_b$ and an actual real symplectic basis of $V_{[\lambda]}$ in which
--   $$A|_{V_{[\lambda]}}=\begin{cases}\mathop{\diamond}_{j=1}^b B(\lambda,q_j,0),&\lambda\in\mathbb R,\\\mathop{\diamond}_{j=1}^b\operatorname{diag}(J_R(\bar\lambda,2q_j)^{-1},J_R(\bar\lambda,2q_j)^T),&\lambda\notin\mathbb R.\end{cases}$$
--   For this fixed representative $\lambda$, the ordered lengths and decomposition are unique, determined by $\dim_{\mathbb C}\ker N_\lambda^r$ for every $r\ge1$. Equivalently the heights in Theorem 9 are $p_j=q_j-1$, and their maximum is the maximal nilpotent height on $E_\lambda$. Negative real eigenvalues are allowed.
--
--
--   This is the complete off-circle normal-form result in the source height convention.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 13, Theorem 9 — normal forms off the unit circle

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

/-- PDF pp.13–14, Theorem 9: both real and nonreal off-circle regimes, all
block lengths and uniqueness. q_j=p_j+1. No erroneous lambda>1 restriction
is imposed on a negative real reciprocal pair. -/
theorem off_circle_normal_forms {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (he : IsEigenvalue A z) (hz : ‖z‖ ≠ 1) :
    OffClassification A z := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
