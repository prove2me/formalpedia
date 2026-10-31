-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_real_even_height_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.real_even_height_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:08:47.861375+00:00
-- url     : https://prove2.me/theorems/89a8d214-06ca-429d-99fe-6dd40d1ce096
-- title:
--   Unnumbered real even-height paired block construction
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   Suppose $a=\pm1$ and $2k$, $k\ge0$, is the maximal height on $E_a$. There exist real vectors $v,w\in E_a$ whose cyclic spaces are individually isotropic, such that
--   $$\Omega((A-aI)^{2k}v,w)=1.$$
--   Their cyclic direct sum is invariant and symplectic of dimension $4k+2$, and has an actual symplectic basis with matrix
--   $$B(a,2k+1,0)=\operatorname{diag}(J(a,2k+1)^{-1},J(a,2k+1)^T).$$
--   The generators are chosen jointly and may mix two initial chains. At $k=0$ the matrix is $aI_2$.
--
--
--   This constructs the paired odd-length real Jordan blocks, including the scalar boundary case.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 15, Unnumbered real even-height paired block construction

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

/-- PDF pp.15–17: existence of the real even-height TWO-chain construction,
including normalized top pairing, isotropic individual cyclic spaces, and the
actual symplectic basis. Generators may mix the two chosen chains. k=0 is included. -/
theorem real_even_height_block {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (a : ℝ) (ha : a = 1 ∨ a = -1) (k : ℕ) (hp : HasNilpotentHeight A (a : ℂ) (2 * k)) :
    ∃ v w : RVec n,
      realEmbed n v ∈ generalizedSpace A (a : ℂ) ∧
      realEmbed n w ∈ generalizedSpace A (a : ℂ) ∧
      omegaR ((realShift A a ^ (2 * k)) v) w = 1 ∧
      (∀ i j : ℕ, omegaR ((realShift A a ^ i) v) ((realShift A a ^ j) v) = 0) ∧
      (∀ i j : ℕ, omegaR ((realShift A a ^ i) w) ((realShift A a ^ j) w) = 0) ∧
      RepresentsR A (cyclicR A a v ⊔ cyclicR A a w) (signedBlock a (2 * k + 1) 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
