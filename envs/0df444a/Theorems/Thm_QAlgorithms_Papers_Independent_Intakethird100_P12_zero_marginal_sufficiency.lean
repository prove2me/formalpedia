-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_zero_marginal_sufficiency
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.zero_marginal_sufficiency
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:49:55.254354+00:00
-- url     : https://prove2.me/theorems/2ab24682-59c6-453d-9f8e-885b8580a8ee
-- title:
--   Proposition 2.4: sufficiency of the zero-marginal perturbation criterion
-- statement:
--   Let $d_1,d_2$ be the dimensions of finite-dimensional complex Hilbert spaces with chosen orthonormal bases. Let $\rho_1,\rho_2$ be positive semidefinite operators of trace one. Write $C(\rho_1,\rho_2)$ for all joint density matrices with these two partial traces, and $E(\rho_1,\rho_2)$ for its extreme points over the real scalars. Coordinates in the tensor product use lexicographic order.
--
--   Let $\rho\in C(\rho_1,\rho_2)$ have rank $k<n$.
--
--   Set $n=d_1d_2$ and $k=\operatorname{rank}\rho$. Let $\sigma$ be a permutation unitary, $A$ a complex $k\times(n-k)$ matrix, and $K$ a strictly positive definite $k\times k$ matrix satisfying
--   $$\sigma\rho\sigma^{-1}=B_A(K),\qquad B_A(L)=\begin{pmatrix}L&LA\\A^\dagger L&A^\dagger LA\end{pmatrix}.$$
--   Here $\dagger$ denotes conjugate transpose. Both marginals of $\sigma^{-1}B_A(L)\sigma$ are computed in the original tensor coordinates.
--
--   Suppose that every Hermitian matrix $L$ of order $k$ satisfies
--   $$\bigl[\operatorname{Tr}_{H_2}(\sigma^{-1}B_A(L)\sigma)=0\ \text{and}\ \operatorname{Tr}_{H_1}(\sigma^{-1}B_A(L)\sigma)=0\bigr]\ \Longrightarrow\ L=0.$$
--   Then
--   $$\rho\in E(\rho_1,\rho_2).$$
--   This supplies the converse to the necessary perturbation condition, without assuming any factorization of midpoint summands.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 7, Proposition 2.4: sufficiency of the zero-marginal perturbation criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Proposition 2.4, PDF p.7: injectivity is a hypothesis, extremality the conclusion.
No midpoint factorization is imposed as an additional hypothesis. -/
theorem zero_marginal_sufficiency {d1 d2 k : ℕ}
    (rho1 : Matrix (Fin d1) (Fin d1) ℂ) (rho2 : Matrix (Fin d2) (Fin d2) ℂ)
    (hm1 : IsDensityMatrix rho1) (hm2 : IsDensityMatrix rho2)
    (rho : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ)
    (hmem : rho ∈ finiteCouplingSet rho1 rho2) (hrank : rho.rank = k)
    (hkn : k < d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) (K : Matrix (Fin k) (Fin k) ℂ)
    (hK : K.PosDef) (hblock : permuteMatrix p (flatMatrix rho) = rankBlockMatrix hkn.le K A)
    (hinjective : NoZeroMarginalPerturbation hkn.le p A) :
    rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
