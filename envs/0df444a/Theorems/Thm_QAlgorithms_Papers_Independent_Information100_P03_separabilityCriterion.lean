-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_separabilityCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P03.separabilityCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:26:34.341978+00:00
-- url     : https://prove2.me/theorems/834de275-061b-4346-a1c8-351708ee8086
-- title:
--   Arbitrary-rank bipartite separability criterion
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
--   If $\rho$ is separable, meaning a finite probability mixture of local pure product densities, then
--
--   $$\|\mathcal Q(\rho)\|_{\rm tr}\le M.$$
--
--   A strict violation certifies bipartite entanglement.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.3, Theorem 1: arbitrary-rank bipartite separability criterion. The
printed complex-Gram proof requires adjoints, but the real-parameter bound is unchanged. -/
theorem separabilityCriterion {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) (hsep : Entanglement.IsSeparableDensity rho) :
    nuclearNorm (enhanced z rho) ≤ separableBound z := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
