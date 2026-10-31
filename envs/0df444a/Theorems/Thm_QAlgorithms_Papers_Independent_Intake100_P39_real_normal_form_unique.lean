-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_real_normal_form_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.real_normal_form_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:11:15.991478+00:00
-- url     : https://prove2.me/theorems/3ebb207b-025a-4b05-b54d-05f265226d66
-- title:
--   Corollary 13 — uniqueness at +/-1
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   Fix $a=\pm1$. Suppose two real symplectic maps have valid signed primary decompositions with data $(r_j,s_j)$ and $(t_j,u_j)$, and their $a$-kernel dimensions at every positive power and all ranks and signatures of $Q^a_{2k}$ agree. Then their signed blocks agree up to a bijection of the block index sets:
--   $$\exists\pi\text{ a bijection},\quad r_j=t_{\pi(j)},\quad s_j=u_{\pi(j)}\quad\text{for every }j.$$
--   The ambient spaces may have other primary components. Applying this to the same map gives uniqueness up to block permutation.
--
--
--   This states complete determination by the computed invariants, without imposing an order among signs of equal-length blocks.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 18, Corollary 13 — uniqueness at +/-1

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

/-- PDF p.18, Corollary 13: complete determination by the COMPUTED data,
with equality of the signed block multiset, not a preferred order of equal sizes. -/
theorem real_normal_form_unique {n N L K : ℕ} (A : GroupedRealMatrix n) (B : GroupedRealMatrix N)
    (hA : IsSymplectic A) (hB : IsSymplectic B) (a : ℝ) (ha : a = 1 ∨ a = -1)
    (r : Fin L → ℕ) (s : Fin L → ℤ) (t : Fin K → ℕ) (u : Fin K → ℤ)
    (hNF : RealNormal A a r s) (hNG : RealNormal B a t u) (hdata : SameRealData A B a) :
    SameBlocks r s t u := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
