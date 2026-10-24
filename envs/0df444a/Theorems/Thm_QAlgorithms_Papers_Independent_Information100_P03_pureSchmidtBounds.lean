-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_pureSchmidtBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P03.pureSchmidtBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:29:10.114989+00:00
-- url     : https://prove2.me/theorems/19da29c2-98fb-4760-ad7a-8c1662a5541c
-- title:
--   Both pure-state Schmidt bounds
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
--   Put $d=\min(d_A,d_B)$. Let $\lambda_k\ge0$ sum to one, and let $(a_k)_{k=0}^{d-1}$ and $(b_k)_{k=0}^{d-1}$ be orthonormal local families. For the normalized Schmidt vector $\phi=\sum_{k=0}^{d-1}\sqrt{\lambda_k}\,a_k\otimes b_k$, both bounds hold:
--
--   $$\|\mathcal Q(|\phi\rangle\langle\phi|)\|_{\rm tr}\le M+2\sum_{0\le i<j<d}\sqrt{\lambda_i\lambda_j},\qquad
--   \|\mathcal Q(|\phi\rangle\langle\phi|)\|_{\rm tr}\le M+d-1.$$
--
--   Zero Schmidt probabilities and unequal local dimensions are allowed, as is $d=1$. The second bound removes dependence on the individual Schmidt probabilities.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 6, Lemma 2; Appendix B pp.14–15

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.6, Lemma 2 (both clauses), Appendix B pp.14--15. Zero Schmidt
probabilities and d=1 are permitted; no equal-dimension assumption is made. -/
theorem pureSchmidtBounds {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (s : SchmidtData dA dB) :
    nuclearNorm (enhanced z (pureDensity (schmidtVector s))) ≤ separableBound z +
      2 * (∑ i : Fin (min dA dB), ∑ j : Fin (min dA dB),
        if i < j then Real.sqrt (s.probability i * s.probability j) else 0) ∧
    nuclearNorm (enhanced z (pureDensity (schmidtVector s))) ≤
      separableBound z + ((min dA dB : ℝ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
