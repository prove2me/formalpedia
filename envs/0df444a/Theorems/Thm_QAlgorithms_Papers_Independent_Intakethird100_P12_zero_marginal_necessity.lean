-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_zero_marginal_necessity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.zero_marginal_necessity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:48:47.070429+00:00
-- url     : https://prove2.me/theorems/fc5a000f-16db-4cf4-8997-76081f117587
-- title:
--   Proposition 2.3: necessity of the zero-marginal perturbation criterion
-- statement:
--   Let $d_1,d_2$ be the dimensions of finite-dimensional complex Hilbert spaces with chosen orthonormal bases. Let $\rho_1,\rho_2$ be positive semidefinite operators of trace one. Write $C(\rho_1,\rho_2)$ for all joint density matrices with these two partial traces, and $E(\rho_1,\rho_2)$ for its extreme points over the real scalars. Coordinates in the tensor product use lexicographic order.
--
--   Let $\rho\in C(\rho_1,\rho_2)$ have rank $k<n$.
--
--   Set $n=d_1d_2$ and $k=\operatorname{rank}\rho$. Let $\sigma$ be a permutation unitary, $A$ a complex $k\times(n-k)$ matrix, and $K$ a strictly positive definite $k\times k$ matrix satisfying
--   $$\sigma\rho\sigma^{-1}=B_A(K),\qquad B_A(L)=\begin{pmatrix}L&LA\\A^\dagger L&A^\dagger LA\end{pmatrix}.$$
--   Here $\dagger$ denotes conjugate transpose. Both marginals of $\sigma^{-1}B_A(L)\sigma$ are computed in the original tensor coordinates.
--
--   If $\rho$ is extreme, then for every Hermitian matrix $L$ of order $k$,
--   $$\operatorname{Tr}_{H_2}(\sigma^{-1}B_A(L)\sigma)=0\ \text{and}\ \operatorname{Tr}_{H_1}(\sigma^{-1}B_A(L)\sigma)=0\quad\Longrightarrow\quad L=0.$$
--   Thus an extreme coupling admits no nonzero Hermitian perturbation in its rank-block coordinates that preserves both marginals.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 5, Proposition 2.3: necessity of the zero-marginal perturbation criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Proposition 2.3, PDF pp.5–6: extremality implies injectivity on Hermitian perturbations. -/
theorem zero_marginal_necessity {d1 d2 k : ℕ}
    (rho1 : Matrix (Fin d1) (Fin d1) ℂ) (rho2 : Matrix (Fin d2) (Fin d2) ℂ)
    (hm1 : IsDensityMatrix rho1) (hm2 : IsDensityMatrix rho2)
    (rho : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ)
    (hmem : rho ∈ finiteCouplingSet rho1 rho2) (hrank : rho.rank = k)
    (hkn : k < d1*d2) (p : Equiv.Perm (Fin (d1*d2)))
    (A : Matrix (Fin k) (Fin (d1*d2-k)) ℂ) (K : Matrix (Fin k) (Fin k) ℂ)
    (hK : K.PosDef) (hblock : permuteMatrix p (flatMatrix rho) = rankBlockMatrix hkn.le K A)
    (hext : rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2)) :
    NoZeroMarginalPerturbation hkn.le p A := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
