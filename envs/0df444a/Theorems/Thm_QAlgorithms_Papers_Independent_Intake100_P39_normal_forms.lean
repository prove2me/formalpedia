-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_normal_forms
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.normal_forms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:01:44.729286+00:00
-- url     : https://prove2.me/theorems/7e5c6772-36ed-4b3b-a152-a24f9566e2ad
-- title:
--   Theorem 1 — Normal forms for symplectic matrices (seed pinned to the full theorem)
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   The space $V$ is the symplectically orthogonal internal direct sum of the $A$-invariant nondegenerate real spaces indexed by the distinct eigenvalue orbits:
--   $$V=\bigoplus_{[\lambda]}V_{[\lambda]},\qquad (V_{[\lambda]})_{\mathbb C}=\bigoplus_{\mu\in[\lambda]}E_\mu.$$
--   At $\lambda=\pm1$ there is one complex summand; at a nonreal unit eigenvalue there are two. The zero-dimensional space has the empty direct sum.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $z\in\mathbb C$, write $R(z)=\left(\begin{smallmatrix}\Re z&-\Im z\\\Im z&\Re z\end{smallmatrix}\right)$. The real Jordan matrix $J_R(z,2r)$ has $R(z)$ on its $2\times2$ diagonal blocks, $I_2$ on its block superdiagonal, and zeros elsewhere.
--   Fix an eigenvalue $\lambda$ off the unit circle. Set $b=\dim_{\mathbb C}\ker N_\lambda$ and let $q$ be the smallest positive exponent annihilating $E_\lambda$. There are $b$ positive integers $q=q_1\ge\cdots\ge q_b$ and an actual real symplectic basis of $V_{[\lambda]}$ in which
--   $$A|_{V_{[\lambda]}}=\begin{cases}\mathop{\diamond}_{j=1}^b B(\lambda,q_j,0),&\lambda\in\mathbb R,\\\mathop{\diamond}_{j=1}^b\operatorname{diag}(J_R(\bar\lambda,2q_j)^{-1},J_R(\bar\lambda,2q_j)^T),&\lambda\notin\mathbb R.\end{cases}$$
--   For this fixed representative $\lambda$, the ordered lengths and decomposition are unique, determined by $\dim_{\mathbb C}\ker N_\lambda^r$ for every $r\ge1$. Equivalently the heights in Theorem 9 are $p_j=q_j-1$, and their maximum is the maximal nilpotent height on $E_\lambda$. Negative real eigenvalues are allowed.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For an eigenvalue $a\in\{1,-1\}$ there are finitely many positive lengths $r_j$ and integers $s_j\in\{-1,0,1\}$, with $s_j=0$ implying $r_j$ odd, and an actual symplectic basis of $V_{[a]}$ such that
--   $$A|_{V_{[a]}}=\mathop{\diamond}_j B(a,r_j,s_j),\qquad\dim\ker(A-aI)=2\#\{j:s_j=0\}+\#\{j:s_j\ne0\}.$$
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   For every $k\ge1$, the positive and negative indices of $Q^a_{2k}$ are respectively $\#\{j:r_j=k,s_j=1\}$ and $\#\{j:r_j=k,s_j=-1\}$. For fixed $a$, the signed block multiset is uniquely determined by all kernel dimensions and all ranks and signatures of these forms; the only freedom is permutation of blocks.
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
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   For each $m\ge1$, the positive and negative indices of $Q^\lambda_m$ are the numbers of signs $+1$ and $-1$ in real blocks of dimension $2m$. For a fixed choice of $\lambda$ versus $\bar\lambda$, the signed block multiset is uniquely determined by the dimensions $\dim_{\mathbb C}\ker N_\lambda^r$ for every $r\ge1$ and by all ranks and signatures of the forms $Q^\lambda_m$. Uniqueness is up to permutation, and the forms may be degenerate.
--
--
--   This is the full real normal-form theorem, including every spectral regime, sign count, and uniqueness assertion.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 3, Theorem 1 — Normal forms for symplectic matrices (seed pinned to the full theorem)

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

/-- PDF pp.3–6, Theorem 1 in full: primary decomposition, every spectral regime,
all eigenspace and sign counts, and determination/uniqueness of the blocks.
No diagonalizability or semisimplicity assumption is made. -/
theorem normal_forms {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    PrimaryDecomposition A ∧
    (∀ z, IsEigenvalue A z → ‖z‖ ≠ 1 → OffClassification A z) ∧
    (∀ a : ℝ, (a = 1 ∨ a = -1) → IsEigenvalue A (a : ℂ) → RealClassification A a) ∧
    (∀ z, IsEigenvalue A z → ‖z‖ = 1 → z ≠ 1 → z ≠ -1 → UnitClassification A z) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
