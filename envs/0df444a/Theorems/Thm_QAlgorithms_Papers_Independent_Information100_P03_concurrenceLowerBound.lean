-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_concurrenceLowerBound
-- name    : QAlgorithms.Papers.Independent.Information100.P03.concurrenceLowerBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:29:59.992977+00:00
-- url     : https://prove2.me/theorems/b9990b1c-a9ee-4cf4-9bf0-cf564b860fd2
-- title:
--   Concurrence lower bound
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
--   Assume $d=\min(d_A,d_B)\ge2$. For a normalized pure vector $\phi$, define $C(\phi)=\sqrt{2(1-\operatorname{Tr}(\rho_A^2))}$, and for a mixed density define $C(\rho)$ by minimizing the average pure concurrence over every normalized pure-state ensemble of $\rho$. Then
--
--   $$C(\rho)\ge\frac{\sqrt2}{\sqrt{d(d-1)}}\bigl(\|\mathcal Q(\rho)\|_{\rm tr}-M\bigr).$$
--
--   This converts the realignment excess into a quantitative entanglement lower bound, without clipping negative values.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 6, Theorem 2; Eqs.(8)–(9) p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.6, Theorem 2, Eqs.(8)--(9) p.5: concurrence lower bound.
The nonzero-denominator regime d>=2 is explicit. -/
theorem concurrenceLowerBound {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (hd : 2 ≤ min dA dB)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) :
    concurrence rho ≥ Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ)) *
      (nuclearNorm (enhanced z rho) - separableBound z) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
