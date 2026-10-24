-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_biseparableCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P03.biseparableCriterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:31:20.752981+00:00
-- url     : https://prove2.me/theorems/0438292e-ecbf-4117-85cb-60203131ae8e
-- title:
--   Biseparable tripartite criterion
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
--   Let $d\ge1$ and let $\rho$ be a density matrix on $(\mathbb C^d)^{\otimes3}$. Use the same real tuple $(P,Q,\mu,\nu)$ satisfying $\nu^T\mu=1$ in all three single-party cuts, and define the scalar
--
--   $$
--   S(\rho)=\frac13\sum_{i\in\{A,B,C\}}\|\mathcal Q^{i\mid\{A,B,C\}\setminus\{i\}}(\rho)\|_{\rm tr}.
--   $$
--
--   In each cut, $\mathcal Q$ is the block matrix defined above, with the single party first and the other two in their original order; its smaller local dimension is $d$.
--
--   If $\rho$ is biseparable, namely a finite probability mixture of normalized pure vectors each product across at least one of the three cuts, then
--
--   $$S(\rho)\le M+\frac{2(d-1)}3.$$
--
--   The cut may vary with the ensemble member. A strict violation certifies genuine tripartite entanglement; $d=1$ is allowed.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 9, Theorem 4; Eqs.(14)–(15)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.9, Theorem 4: the cut may vary between biseparable ensemble members.
Each cut has smaller Hilbert dimension d, not d squared. -/
theorem biseparableCriterion {d m n r : ℕ} [NeZero d]
    (z : Parameters m n r) (rho : Matrix (Tripartite d) (Tripartite d) ℂ)
    (hrho : IsDensityMatrix rho) (hbisep : IsBiseparable rho) :
    tripartiteScore z rho ≤ separableBound z + 2 * ((d : ℝ) - 1) / 3 := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
