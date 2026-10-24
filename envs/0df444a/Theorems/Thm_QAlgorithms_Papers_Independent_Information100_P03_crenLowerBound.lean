-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_crenLowerBound
-- name    : QAlgorithms.Papers.Independent.Information100.P03.crenLowerBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:30:43.834991+00:00
-- url     : https://prove2.me/theorems/4a4e62e7-a0aa-4ede-9ac5-9cf8becfe0af
-- title:
--   Normalized CREN lower bound
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
--   Assume $d=\min(d_A,d_B)\ge2$. Let $T_B$ be partial transpose on subsystem B. Define $N(\phi)=(\|T_B(|\phi\rangle\langle\phi|)\|_{\rm tr}-1)/(d-1)$ for normalized pure vectors, and define $N(\rho)$ as the convex roof of this pure cost. Then
--
--   $$N(\rho)\ge\frac{\|\mathcal Q(\rho)\|_{\rm tr}-M}{d-1}.$$
--
--   The normalization gives one on maximally entangled pure d-states. For mixed densities this measure is the convex-roof extension, rather than the partial-transpose norm itself.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 6, Theorem 3; Eqs.(10)–(11) p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.6, Theorem 3, Eqs.(10)--(11) p.5: NORMALIZED convex-roof extended
negativity lower bound, with d>=2 and without clipping its right-hand side. -/
theorem crenLowerBound {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (hd : 2 ≤ min dA dB)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) :
    cren rho ≥ (nuclearNorm (enhanced z rho) - separableBound z) /
      ((min dA dB : ℝ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
