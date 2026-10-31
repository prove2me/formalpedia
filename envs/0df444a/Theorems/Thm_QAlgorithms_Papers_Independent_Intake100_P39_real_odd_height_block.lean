-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_real_odd_height_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.real_odd_height_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:08:23.491418+00:00
-- url     : https://prove2.me/theorems/4a435440-4708-41f4-9953-c512004c976c
-- title:
--   Unnumbered real odd-height signed block construction
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   Suppose $a=\pm1$ and $2k-1$, $k\ge1$, is the maximal height on $E_a$. Let $v$ be a real vector of that height with $\Omega((A-aI)^{2k-1}v,v)\ne0$. There exist $s\in\{1,-1\}$ and a real generator $v'$ of the same cyclic space, of the same height, such that
--   $$Q^a_{2k}(v',v')=s,\qquad\Omega((A-aI)^iv',(A-aI)^jv')=0\quad(0\le i,j<k).$$
--   The original real cyclic space is symplectic, has dimension $2k$, and has an actual symplectic basis with matrix $B(a,k,s)$. The normalization and its sign are conclusions.
--
--
--   This is the signed odd-height cyclic block construction with its legitimate nonzero top-pairing input.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 14, Unnumbered real odd-height signed block construction

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

/-- PDF pp.14–15: real odd-height construction. Only the nonzero TOP pairing
is an input; the normalization, its sign, and the basis are all CONCLUSIONS. -/
theorem real_odd_height_block {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (a : ℝ) (ha : a = 1 ∨ a = -1) (k : ℕ) (hk : 0 < k)
    (v : RVec n) (hpmax : HasNilpotentHeight A (a : ℂ) (2 * k - 1))
    (hp : VectorHeight A (a : ℂ) (realEmbed n v) (2 * k - 1))
    (hpair : omegaR ((realShift A a ^ (2 * k - 1)) v) v ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (∃ vnew : RVec n, cyclicR A a vnew = cyclicR A a v ∧
        VectorHeight A (a : ℂ) (realEmbed n vnew) (2 * k - 1) ∧
        realQ A a k vnew vnew = (s : ℝ) ∧
        ∀ i < k, ∀ j < k, omegaR ((realShift A a ^ i) vnew) ((realShift A a ^ j) vnew) = 0) ∧
      RepresentsR A (cyclicR A a v) (signedBlock a k (s : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
