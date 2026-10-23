-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_rankAndSpecializations
-- name    : QAlgorithms.Papers.Independent.Information100.P03.rankAndSpecializations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:32:40.140377+00:00
-- url     : https://prove2.me/theorems/9553ed8e-b507-48be-8e18-38d3b3656adf
-- title:
--   Rank and recovery of all three earlier block matrices
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
--   For every density $\rho$, the construction has the following four properties:
--
--   1. If $m,n\ge r$ and both P and Q have column rank r, then $\operatorname{rank}(PQ^T)=r$.
--   2. With $m=n=r=1$, $\mu=\nu=1$, $P=\alpha$, $Q=\beta$, it is Eq.(2): the rank-one border with scalar $\alpha\beta$, top-right $\alpha\operatorname{vec}(\rho_B)^T$, bottom-left $\beta\operatorname{vec}(\rho_A)$, and lower-right $R(\rho)$.
--   3. With $r=1$, $\mu=\nu=1$, $m=n=l$, and constant columns $P=\alpha\mathbf1_l$, $Q=\beta\mathbf1_l$, it is Eq.(3): the same border with upper-left $\alpha\beta\mathbf1_l\mathbf1_l^T$ and repeated marginal columns.
--   4. With $r=1$, $\mu=\nu=1$, $P=a\in\mathbb R^m$, $Q=b\in\mathbb R^n$, it is Eq.(4), with blocks $ab^T$, $a\operatorname{vec}(\rho_B)^T$, $\operatorname{vec}(\rho_A)b^T$, and $R(\rho)$.
--
--   The three matrix identities hold without rank assumptions and hold for every real scalar or vector parameter. They explain the unification of the earlier criteria.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 3, Paragraph after Eq.(5), Eqs.(2)–(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.3, paragraph following Eq.(5): rank statement and ALL three
specializations. Full-column-rank hypotheses occur only in the rank clause. -/
theorem rankAndSpecializations {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hrho : IsDensityMatrix rho) :
    ((r ≤ m ∧ r ≤ n ∧ Matrix.rank z.P = r ∧ Matrix.rank z.Q = r) →
      Matrix.rank (z.P * z.Q.transpose) = r) ∧
    (∀ alpha beta : ℝ,
      enhanced (rankOneParameters (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta)) rho =
        rankOneBlock (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta) rho) ∧
    (∀ (l : ℕ) (alpha beta : ℝ), 0 < l →
      enhanced (rankOneParameters (fun _ : Fin l => alpha) (fun _ : Fin l => beta)) rho =
        rankOneBlock (fun _ : Fin l => alpha) (fun _ : Fin l => beta) rho) ∧
    (∀ (a : Fin m → ℝ) (b : Fin n → ℝ),
      enhanced (rankOneParameters a b) rho = rankOneBlock a b rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
