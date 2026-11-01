-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_general_extremality_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.general_extremality_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:47:37.708422+00:00
-- url     : https://prove2.me/theorems/546c90e8-6824-4e48-8889-85b97ef2ddbc
-- title:
--   Theorem 2.5: general extremality criterion and rank bound
-- statement:
--   Let $d_1,d_2$ be the dimensions of finite-dimensional complex Hilbert spaces with chosen orthonormal bases. Let $\rho_1,\rho_2$ be positive semidefinite operators of trace one. Write $C(\rho_1,\rho_2)$ for all joint density matrices with these two partial traces, and $E(\rho_1,\rho_2)$ for its extreme points over the real scalars. Coordinates in the tensor product use lexicographic order.
--
--   For every $\rho\in C(\rho_1,\rho_2)$ of rank $k$, extremality necessarily implies
--   $$k\le\sqrt{d_1^2+d_2^2-1}.$$
--   For every rank-block representation below, allowing $k=n$ and then a zero-column $A$, the following criterion holds.
--
--   Set $n=d_1d_2$ and $k=\operatorname{rank}\rho$. Let $\sigma$ be a permutation unitary, $A$ a complex $k\times(n-k)$ matrix, and $K$ a strictly positive definite $k\times k$ matrix satisfying
--   $$\sigma\rho\sigma^{-1}=B_A(K),\qquad B_A(L)=\begin{pmatrix}L&LA\\A^\dagger L&A^\dagger LA\end{pmatrix}.$$
--   Here $\dagger$ denotes conjugate transpose. Both marginals of $\sigma^{-1}B_A(L)\sigma$ are computed in the original tensor coordinates.
--
--   Put $R=[I_k\mid A]$ and
--   $$D=\{R\sigma(X_1\otimes I_{d_2}+I_{d_1}\otimes X_2)\sigma^{-1}R^\dagger:X_1=X_1^\dagger,\ X_2=X_2^\dagger\}.$$
--   Then
--   $$\rho\in E(\rho_1,\rho_2)\quad\Longleftrightarrow\quad D=\operatorname{Herm}(k),$$
--   where $\operatorname{Herm}(k)$ is the real vector space of all Hermitian matrices of order $k$. This characterizes extremality by a concrete finite-dimensional image and also bounds the possible ranks.
--
--   **Formalization Note** The printed column $[I;A^t]$ is changed to $[I;A^\dagger]$, following (2.11) on PDF p.6 and the $AXA^\dagger$ expansion on PDF p.11. This correction requires independent moderation.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 7, Theorem 2.5: general extremality criterion and rank bound (original abstract seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Theorem 2.5, PDF pp.7–8: BOTH the rank bound and full iff criterion.
Printed D ends with [I;A^t]; changed to [I;A†], required by (2.11), PDF p.6,
and the AXA† expansion, PDF p.11. Independent moderation of this correction is pending.
Here k=n is allowed, with zero-column A. -/
theorem general_extremality_criterion {d1 d2 k : ℕ}
    (rho1 : Matrix (Fin d1) (Fin d1) ℂ) (rho2 : Matrix (Fin d2) (Fin d2) ℂ)
    (hm1 : IsDensityMatrix rho1) (hm2 : IsDensityMatrix rho2)
    (rho : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ)
    (hmem : rho ∈ finiteCouplingSet rho1 rho2) (hrank : rho.rank = k) :
    (rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2) →
      (k : ℝ) ≤ Real.sqrt ((d1 : ℝ)^2 + (d2 : ℝ)^2 - 1)) ∧
    ∀ (hkn : k ≤ d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
      (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) (K : Matrix (Fin k) (Fin k) ℂ),
      K.PosDef → permuteMatrix p (flatMatrix rho) = rankBlockMatrix hkn K A →
      (rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2) ↔
        compressedLocalSpace hkn p A = {L | L.IsHermitian}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
