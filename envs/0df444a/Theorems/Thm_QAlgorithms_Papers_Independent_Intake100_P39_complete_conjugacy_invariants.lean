-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_complete_conjugacy_invariants
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.complete_conjugacy_invariants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:02:33.36961+00:00
-- url     : https://prove2.me/theorems/19356e61-3cdf-4cd0-8751-aad1dcf48975
-- title:
--   Theorem 2 — complete symplectic conjugacy invariants
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   For two symplectic maps $A,B$ on the same $V$, the following equivalence holds:
--   $$A\text{ and }B\text{ are symplectically conjugate}\quad\Longleftrightarrow\quad\text{their spectral, kernel, rank, and signature data agree}.$$
--   The data consist of the same eigenvalues, all $\dim_{\mathbb C}\ker N_\lambda^r$ for $r\ge1$, all ranks and signatures of $Q^{\pm1}_{2k}$ for $k\ge1$, and all ranks and signatures of $Q^\lambda_m$ for nonreal unit eigenvalues and $m\ge1$. The draft compares all eigenvalues redundantly, equivalent to making consistent choices of orbit representatives for both maps. All data are computed from each map itself. Symplectic conjugacy means there is a symplectic $P$ with $BP=PA$.
--
--
--   This is completeness of the invariants, as well as their invariance under conjugation.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 6, Theorem 2 — complete symplectic conjugacy invariants

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

/-- PDF p.6, Theorem 2: the listed data are COMPLETE invariants, in both directions.
All eigenvalues are compared redundantly, equivalent to fixing common orbit representatives. -/
theorem complete_conjugacy_invariants {n : ℕ} (A B : GroupedRealMatrix n)
    (hA : IsSymplectic A) (hB : IsSymplectic B) :
    SymplecticallyConjugate A B ↔ SameInvariants A B := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
