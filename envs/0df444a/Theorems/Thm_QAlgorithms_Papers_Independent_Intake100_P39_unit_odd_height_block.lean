-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_odd_height_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_odd_height_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:11:39.59191+00:00
-- url     : https://prove2.me/theorems/72f872c1-a5d3-42dd-845f-cd6a5207cb88
-- title:
--   Unnumbered unit-circle odd-height real block construction, equations (23)–(25)
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
--   Put $P=\operatorname{diag}(J(\bar\lambda,k),J(\lambda,k))$ and $D=D(k,s)$. The complex matrix in (23) is $\left(\begin{smallmatrix}P^{-1}&P^{-1}\left(\begin{smallmatrix}0&D\\D&0\end{smallmatrix}\right)\\0&P^T\end{smallmatrix}\right)$.
--   Let $\lambda$ be nonreal of unit norm and let the maximal height be $2k-1$, $k\ge1$. If $v$ has that height and $\Omega_{\mathbb C}(N_\lambda^{2k-1}v,\bar v)\ne0$, there are a sign $s=\pm1$ and a generator $v'$ of the same cyclic space with the same height, $Q^\lambda_{2k}(v',v')=s$, and $T_{ij}(v')=0$ for $0\le i,j<k$. The conjugate cyclic sum has the conjugate-paired complex symplectic basis (23). Its real part has dimension $4k$ and an actual real symplectic basis representing $A$ by
--   $$M_{2k}(\lambda,s).$$
--   The argument of both diagonal $J_R$ terms is $\bar\lambda$; formula (25) specifies $C_R^T$, not $C_R$.
--
--
--   This retains the complex block, its real structure, and the real signed cyclic block.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 18, Unnumbered unit-circle odd-height real block construction, equations (23)–(25)

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

/-- PDF pp.18–20, (23)–(25): odd-height complex and REAL blocks.
The normalization and its sign are concluded from the chosen nonzero top pairing.
(25) describes C_R transpose; realification uses bar(lambda) in (24). -/
theorem unit_odd_height_block {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hreal : z.im ≠ 0) (k : ℕ) (hk : 0 < k)
    (v : CVec n) (hpmax : HasNilpotentHeight A z (2 * k - 1))
    (hp : VectorHeight A z v (2 * k - 1))
    (hpair : omegaC ((shifted A z ^ (2 * k - 1)) v) (star v) ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (∃ vnew : CVec n, cyclicC A z vnew = cyclicC A z v ∧
        VectorHeight A z vnew (2 * k - 1) ∧ unitQ A z (2 * k) vnew vnew = (s : ℂ) ∧
        ∀ i < k, ∀ j < k, chainT A z vnew i j = 0) ∧
      PairedEvenRepresentation A (cyclicC A z v ⊔ cyclicC A (star z) (star v)) z k s ∧
      RepresentsR A (realPart (cyclicC A z v ⊔ cyclicC A (star z) (star v)))
        (unitEvenBlock z k (s : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
