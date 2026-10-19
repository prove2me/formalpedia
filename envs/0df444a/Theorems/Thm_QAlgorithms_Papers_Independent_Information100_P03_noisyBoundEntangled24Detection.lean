-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_noisyBoundEntangled24Detection
-- name    : QAlgorithms.Papers.Independent.Information100.P03.noisyBoundEntangled24Detection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:22.278984+00:00
-- url     : https://prove2.me/theorems/b3c751ce-7bbf-4e33-b538-01ca82c82328
-- title:
--   Noisy 2-by-4 bound-entangled mixture: all Table I intervals
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
--   Use the lexicographic basis $|00\rangle,\ldots,|03\rangle,|10\rangle,\ldots,|13\rangle$ of $\mathbb C^2\otimes\mathbb C^4$. At $a=0.9$, let
--
--   $$\rho_a=\frac1{1+7a}\begin{pmatrix}a&0&0&0&0&a&0&0\0&a&0&0&0&0&a&0\0&0&a&0&0&0&0&a\0&0&0&a&0&0&0&0\0&0&0&0&(1+a)/2&0&0&\sqrt{1-a^2}/2\a&0&0&0&0&a&0&0\0&a&0&0&0&0&a&0\0&0&a&0&\sqrt{1-a^2}/2&0&0&(1+a)/2\end{pmatrix},\quad \xi=\frac{|00\rangle+|11\rangle}{\sqrt2},\quad\rho_x=(1-x)\rho_a+x|\xi\rangle\langle\xi|.$$
--
--   The five witnesses are: (i) our matrix with $P=\left(\begin{smallmatrix}9.28&10.51\10.44&10.65\end{smallmatrix}\right)$, $Q=\left(\begin{smallmatrix}10.01&12.75\13.03&13.54\end{smallmatrix}\right)$ and $\mu=\nu=(1,1)^T/\sqrt2$; (ii) the rank-one border with $a=(11.9967,12.9195,11.6808,12.1705,11.4476)^T$, $b=(12.5025,11.5102,12.0119,12.3982,12.7818)^T$; (iii) constant borders $10\mathbf1_5$, $12\mathbf1_5$; (iv) scalar borders 10,12; (v) ordinary realignment with bound one. For each witness, its sufficient closed interval is
--
--   $$\begin{array}{c|c}\text{criterion}&\text{detected interval}\\hline\text{our theorem}&0.223231\le x\le1\[31]&0.232959\le x\le1\[30]&0.223267\le x\le1\[29]&0.223276\le x\le1\[18]&0.252746\le x\le1\end{array}.$$
--
--   Throughout its listed interval the corresponding trace norm strictly exceeds its separability bound and $\rho_x$ is entangled. These are sufficient intervals, without an optimality or converse claim. The first interval contains every earlier listed interval.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 4, Example 1 and Table I

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.4, Example 1 and ALL rows of Table I: sufficient closed intervals,
strict detection by the displayed witnesses, and entanglement. No converse or
optimal-root assertion is made. -/
theorem noisyBoundEntangled24Detection (i : Fin 5) (x : ℝ)
    (hx : exampleOneCutoff i ≤ x) (hxOne : x ≤ 1) :
    0 < bipartiteViolation (exampleOneChoice i) (exampleOneState x) ∧
      ¬ Entanglement.IsSeparableDensity (exampleOneState x) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
