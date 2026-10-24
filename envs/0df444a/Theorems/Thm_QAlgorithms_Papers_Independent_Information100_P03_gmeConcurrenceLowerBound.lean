-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_gmeConcurrenceLowerBound
-- name    : QAlgorithms.Papers.Independent.Information100.P03.gmeConcurrenceLowerBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:32:04.599993+00:00
-- url     : https://prove2.me/theorems/2a6f42e1-f66a-4194-9ce4-6a560cf8d0a7
-- title:
--   GME concurrence lower bound
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
--   Assume $d\ge2$. For a normalized pure vector $\phi$, let $\rho_i$ be its reduced density on party i and define $C_{\rm GME}(\phi)=\min_{i=A,B,C}\sqrt{1-\operatorname{Tr}(\rho_i^2)}$. For a mixed density take the convex roof of that cost. Then
--
--   $$C_{\rm GME}(\rho)\ge\frac1{\sqrt{d(d-1)}}\left(S(\rho)-M-\frac{2(d-1)}3\right).$$
--
--   This lower bound uses the minimum over reduced purities, without a factor of $\sqrt2$, and requires no biseparability assumption.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 11, Theorem 6; Eqs.(18)–(19) p.10; Appendix C pp.15–16

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.11, Theorem 6, Eq.(18)--(19) p.10: GME concurrence lower bound.
The offset remains inside the prefactor and the pure cost uses the minimum. -/
theorem gmeConcurrenceLowerBound {d m n r : ℕ} [NeZero d]
    (z : Parameters m n r) (hd : 2 ≤ d)
    (rho : Matrix (Tripartite d) (Tripartite d) ℂ) (hrho : IsDensityMatrix rho) :
    gmeConcurrence rho ≥ 1 / Real.sqrt (((d : ℝ) - 1) * (d : ℝ)) *
      (tripartiteScore z rho - separableBound z - 2 * ((d : ℝ) - 1) / 3) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
