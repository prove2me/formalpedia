-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_unit_circle_normal_form_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.unit_circle_normal_form_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:14:50.139433+00:00
-- url     : https://prove2.me/theorems/b64f75a2-f7f7-4b8c-990f-9228f47c24fc
-- title:
--   Corollary 18 — unit-circle uniqueness and complete invariants
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $|\lambda|=1$, $\lambda\ne\pm1$, and $m\ge1$, define on $\ker N_\lambda^m$ the form
--   $$Q^\lambda_m(v,w)=\begin{cases}\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k-1}\bar w),&m=2k,\\i\,\Omega_{\mathbb C}(N_\lambda^k v,N_{\bar\lambda}^{k}\bar w),&m=2k+1.\end{cases}$$
--   It is linear in its first argument and conjugate-linear in its second. Positive and negative indices are complex dimensions of maximal definite complex subspaces; rank is their sum and signature their difference.
--   Fix the same nonreal unit eigenvalue $\lambda$ for two real symplectic maps. Suppose their primary signed decompositions have lengths and signs $(m_j,s_j)$ and $(t_j,u_j)$. If every $\lambda$-kernel dimension and every rank and signature of $Q^\lambda_m$ agree, then
--   $$\exists\pi\text{ a bijection},\quad m_j=t_{\pi(j)},\quad s_j=u_{\pi(j)}\quad\text{for every }j.$$
--   For the same map this gives uniqueness up to permutation. The choice of $\lambda$ versus $\bar\lambda$ must be held fixed; degenerate forms are allowed.
--
--
--   This is complete determination and uniqueness of the nonreal unit-circle signed decomposition.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 26, Corollary 18 — unit-circle uniqueness and complete invariants

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

/-- PDF p.26, Corollary 18: complete invariants and uniqueness up to a
permutation, with the SAME chosen lambda, and possibly degenerate forms. -/
theorem unit_circle_normal_form_unique {n N L K : ℕ} (A : GroupedRealMatrix n) (B : GroupedRealMatrix N)
    (hA : IsSymplectic A) (hB : IsSymplectic B) (z : ℂ)
    (hz : ‖z‖ = 1) (hplus : z ≠ 1) (hminus : z ≠ -1)
    (m : Fin L → ℕ) (s : Fin L → ℤ) (t : Fin K → ℕ) (u : Fin K → ℤ)
    (hNF : UnitNormal A z m s) (hNG : UnitNormal B z t u) (hdata : SameUnitData A B z) :
    SameBlocks m s t u := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
