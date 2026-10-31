-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_circle_normal_form
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_circle_normal_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:13:21.64299+00:00
-- url     : https://prove2.me/theorems/209b063f-fd7b-4201-8ae6-791946953548
-- title:
--   Theorem 15 — real normal forms on the nonreal unit-circle primary space
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $z\in\mathbb C$, write $R(z)=\left(\begin{smallmatrix}\Re z&-\Im z\\\Im z&\Re z\end{smallmatrix}\right)$. The real Jordan matrix $J_R(z,2r)$ has $R(z)$ on its $2\times2$ diagonal blocks, $I_2$ on its block superdiagonal, and zeros elsewhere.
--   For $|\lambda|=1$ and $\Im\lambda\ne0$, let the two-column matrix $V_k=(V_k^1\ V_k^2)$ have row-block $h$, $0\le h<k$, equal to $(-1)^{k-1-h}R(\lambda^{k-h})$, and set $U_k=(U_k^1\ U_k^2)=V_kR(\lambda)$. With $J_R=J_R(\bar\lambda,2k)$, the even-chain block is
--   $$M_{2k}(\lambda,s)=\begin{pmatrix}J_R^{-1}&C\\0&J_R^T\end{pmatrix},\qquad C=(0\ \cdots\ 0\ sV_k^1\ sV_k^2),\quad k\ge1.$$
--   For odd chain length the block, in row and column sizes $(2k,1,2k,1)$, is
--   $$M_{2k+1}(\lambda,s)=\begin{pmatrix}J_R^{-1}&sU_k^2&E&U_k^1\\0&\Re\lambda&e_o^T&s\Im\lambda\\0&0&J_R^T&0\\0&-s\Im\lambda&-s e_e^T&\Re\lambda\end{pmatrix},\quad k\ge0.$$
--   Here $E$ has last two columns $(s/2)V_k^2$ and $-(s/2)V_k^1$ and other columns zero, while $e_o,e_e$ are the penultimate and last standard vectors in $\mathbb R^{2k}$. For $k=0$ these empty sectors are omitted, leaving $\left(\begin{smallmatrix}\Re\lambda&s\Im\lambda\\-s\Im\lambda&\Re\lambda\end{smallmatrix}\right)$. In both families $s\in\{1,-1\}$ and real block dimension is twice the chain length.
--   For every nonreal unit eigenvalue $\lambda$, an actual real symplectic basis of $V_{[\lambda]}$ represents its restriction as a finite symplectic sum of the displayed blocks:
--   $$A|_{V_{[\lambda]}}=\mathop{\diamond}_j M_{m_j}(\lambda,s_j),\qquad m_j\ge1,\quad s_j\in\{1,-1\},\quad\dim_{\mathbb C}\ker N_\lambda=\#\{j\}.$$
--   Even $m_j=2k$ uses $k\ge1$; odd $m_j=2k+1$ uses $k\ge0$.
--
--
--   This is the full real unit-circle block catalogue and its eigenspace count; uniqueness belongs to Corollary 18.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 25, Theorem 15 — real normal forms on the nonreal unit-circle primary space

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

/-- PDF pp.25–26, Theorem 15: the TWO exact real block families, with one
complex lambda-eigenvector per block. Uniqueness is stated separately. -/
theorem unit_circle_normal_form {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (he : IsEigenvalue A z) (hz : ‖z‖ = 1) (hplus : z ≠ 1) (hminus : z ≠ -1) :
    ∃ (L : ℕ) (m : Fin L → ℕ) (s : Fin L → ℤ),
      UnitNormal A z m s ∧ kernelDim A z 1 = L := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
