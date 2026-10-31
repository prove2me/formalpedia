-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_even_height_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_even_height_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:12:02.898655+00:00
-- url     : https://prove2.me/theorems/14289a82-d14e-48bc-8f2c-b354faf0b324
-- title:
--   Unnumbered unit-circle even-height real block construction, equations (26)–(28) and p.25
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $|\lambda|=1$, define
--   $$T_{ij}(v)=\frac{\Omega_{\mathbb C}(N_\lambda^i v,N_{\bar\lambda}^j\bar v)}{\lambda^i\bar\lambda^j},\qquad i,j\ge0.$$
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   For $z\in\mathbb C$, write $R(z)=\left(\begin{smallmatrix}\Re z&-\Im z\\\Im z&\Re z\end{smallmatrix}\right)$. The real Jordan matrix $J_R(z,2r)$ has $R(z)$ on its $2\times2$ diagonal blocks, $I_2$ on its block superdiagonal, and zeros elsewhere.
--   For $|\lambda|=1$ and $\Im\lambda\ne0$, let the two-column matrix $V_k=(V_k^1\ V_k^2)$ have row-block $h$, $0\le h<k$, equal to $(-1)^{k-1-h}R(\lambda^{k-h})$, and set $U_k=(U_k^1\ U_k^2)=V_kR(\lambda)$. With $J_R=J_R(\bar\lambda,2k)$, the even-chain block is
--   $$M_{2k}(\lambda,s)=\begin{pmatrix}J_R^{-1}&C\\0&J_R^T\end{pmatrix},\qquad C=(0\ \cdots\ 0\ sV_k^1\ sV_k^2),\quad k\ge1.$$
--   For odd chain length the block, in row and column sizes $(2k,1,2k,1)$, is
--   $$M_{2k+1}(\lambda,s)=\begin{pmatrix}J_R^{-1}&sU_k^2&E&U_k^1\\0&\Re\lambda&e_o^T&s\Im\lambda\\0&0&J_R^T&0\\0&-s\Im\lambda&-s e_e^T&\Re\lambda\end{pmatrix},\quad k\ge0.$$
--   Here $E$ has last two columns $(s/2)V_k^2$ and $-(s/2)V_k^1$ and other columns zero, while $e_o,e_e$ are the penultimate and last standard vectors in $\mathbb R^{2k}$. For $k=0$ these empty sectors are omitted, leaving $\left(\begin{smallmatrix}\Re\lambda&s\Im\lambda\\-s\Im\lambda&\Re\lambda\end{smallmatrix}\right)$. In both families $s\in\{1,-1\}$ and real block dimension is twice the chain length.
--   Put $P=\operatorname{diag}(J(\bar\lambda,k),J(\lambda,k+1))$ and let $S$ be the $k\times(k+1)$ matrix with only its last row possibly nonzero, ending in $(is/2,\lambda is)$. The complex matrix in (27) is $\left(\begin{smallmatrix}P^{-1}&P^{-1}\left(\begin{smallmatrix}0&S\\S^T&0\end{smallmatrix}\right)\\0&P^T\end{smallmatrix}\right)$. At $k=0$ the rectangular sectors are empty.
--   Let $\lambda$ be nonreal of unit norm and let the maximal height be $2k$, $k\ge0$. If $v$ has that height and $\Omega_{\mathbb C}(N_\lambda^{2k}v,\bar v)\ne0$, there are a sign $s=\pm1$ and a generator $v'$ of the same cyclic space and height such that
--   $$Q^\lambda_{2k+1}(v',v')=s,\qquad T_{ij}(v')=0\ (i,j<k),\qquad T_{k,k-1}(v')=si/2\ (k>0).$$
--   The conjugate cyclic sum has the complex symplectic basis (27); its central pair obeys $b'_k=-is\,\overline{a'_k}$. Its real part has dimension $4k+2$ and an actual real symplectic basis representing $A$ by $M_{2k+1}(\lambda,s)$.
--
--
--   This preserves the first-slot conjugation normalization on p.21 and the sign on p.25, including the planar case.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 21, Unnumbered unit-circle even-height real block construction, equations (26)–(28) and p.25

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

/-- PDF pp.21–25, (26)–(28): even-height blocks, including k=0. The sign and
normalization are conclusions. First-slot conjugation on p.21 gives the same
sign as i Omega(N^k v,conjugate(N^k v)) on p.25. -/
theorem unit_even_height_block {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hreal : z.im ≠ 0) (k : ℕ)
    (v : CVec n) (hpmax : HasNilpotentHeight A z (2 * k))
    (hp : VectorHeight A z v (2 * k))
    (hpair : omegaC ((shifted A z ^ (2 * k)) v) (star v) ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (∃ vnew : CVec n, cyclicC A z vnew = cyclicC A z v ∧
        VectorHeight A z vnew (2 * k) ∧ unitQ A z (2 * k + 1) vnew vnew = (s : ℂ) ∧
        (0 < k → chainT A z vnew k (k - 1) = (s : ℂ) * Complex.I / 2) ∧
        ∀ i < k, ∀ j < k, chainT A z vnew i j = 0) ∧
      PairedOddRepresentation A (cyclicC A z v ⊔ cyclicC A (star z) (star v)) z k s ∧
      RepresentsR A (realPart (cyclicC A z v ⊔ cyclicC A (star z) (star v)))
        (unitOddBlock z k (s : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
