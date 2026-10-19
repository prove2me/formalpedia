-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_hilbertSchmidtRelaxation
-- name    : QAlgorithms.Papers.Independent.Information100.P03.hilbertSchmidtRelaxation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:28:25.601326+00:00
-- url     : https://prove2.me/theorems/41b03be6-aadd-4a23-9352-b1cea6a3a964
-- title:
--   Hilbert–Schmidt relaxation of the separability bound
-- statement:
--   Let $d_A,d_B\ge1$ be finite local dimensions and let $P\in\mathbb R^{m\times r}$, $Q\in\mathbb R^{n\times r}$, $\mu,\nu\in\mathbb R^r$ satisfy $\nu^T\mu=1$. The auxiliary row counts $m,n$ are independent of the local dimensions; no rank assumption is imposed. For a bipartite density matrix $\rho$ (positive semidefinite with trace one), write $\rho_A=\operatorname{Tr}_B\rho$ and $\rho_B=\operatorname{Tr}_A\rho$. Column vectorization stacks columns, and realignment satisfies $R(X\otimes Y)=\operatorname{vec}(X)\operatorname{vec}(Y)^T$, with an ordinary transpose. Define
--
--   $$
--   \mathcal Q(\rho)=\begin{pmatrix}PQ^T&P\mu\operatorname{vec}(\rho_B)^T\\operatorname{vec}(\rho_A)\nu^TQ^T&R(\rho)\end{pmatrix},\qquad
--   M=\left\|(P^TP+\nu\nu^T)^{1/2}(Q^TQ+\mu\mu^T)^{1/2}\right\|_{\rm tr}.
--   $$
--
--   Here the square roots are the positive semidefinite square roots and $\|\cdot\|_{\rm tr}$ denotes the sum of singular values, including for rectangular matrices.
--
--   If $\rho$ is separable, then
--
--   $$\|\mathcal Q(\rho)\|_{\rm tr}\le\sqrt{\|P\|_F^2+\|\nu\|_2^2}\sqrt{\|Q\|_F^2+\|\mu\|_2^2}.$$
--
--   Here $\|P\|_F^2=\sum_{i,j}|P_{ij}|^2$ is the squared Hilbert–Schmidt norm, and the vector norms are Euclidean. This provides a scalar relaxation of the matrix square-root bound.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 4, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.4, Corollary 1: the Hilbert--Schmidt relaxation uses Frobenius norms. -/
theorem hilbertSchmidtRelaxation {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) (hsep : Entanglement.IsSeparableDensity rho) :
    nuclearNorm (enhanced z rho) ≤
      Real.sqrt (frobNorm (fun i j => (z.P i j : ℂ)) ^ 2 + ∑ k, z.nu k ^ 2) *
      Real.sqrt (frobNorm (fun i j => (z.Q i j : ℂ)) ^ 2 + ∑ k, z.mu k ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
