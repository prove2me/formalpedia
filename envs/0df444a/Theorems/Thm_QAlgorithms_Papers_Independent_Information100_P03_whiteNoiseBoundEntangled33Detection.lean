-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_whiteNoiseBoundEntangled33Detection
-- name    : QAlgorithms.Papers.Independent.Information100.P03.whiteNoiseBoundEntangled33Detection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:54.235413+00:00
-- url     : https://prove2.me/theorems/4a497e65-ff1b-4cdc-8050-47151d2885f6
-- title:
--   White-noise 3-by-3 mixture: all five Table II rows and columns
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
--   On $\mathbb C^3\otimes\mathbb C^3$ in lexicographic order, let
--
--   $$\rho_t=\frac1{1+8t}\begin{pmatrix}t&0&0&0&t&0&0&0&t\0&t&0&0&0&0&0&0&0\0&0&t&0&0&0&0&0&0\0&0&0&t&0&0&0&0&0\t&0&0&0&t&0&0&0&t\0&0&0&0&0&t&0&0&0\0&0&0&0&0&0&(1+t)/2&0&\sqrt{1-t^2}/2\0&0&0&0&0&0&0&t&0\t&0&0&0&t&0&\sqrt{1-t^2}/2&0&(1+t)/2\end{pmatrix},\qquad\rho_p=(1-p)I_9/9+p\rho_t.$$
--
--   Our auxiliary matrices and vectors are
--
--   $$P=\begin{pmatrix}3.511157&1.621537\0.8302&2.934043\1.626937&2.083113\2.058475&2.54207\2.053231&1.890969\2.197353&3.218868\end{pmatrix},\quad Q=\begin{pmatrix}3.317891&1.579999\1.533877&1.714491\2.860596&3.503382\2.042115&3.078828\0.519943&3.29257\1.828804&0.217855\end{pmatrix},\quad\mu=\nu=(1,1)^T/\sqrt2.$$
--
--   For comparison, [18] is ordinary realignment; [29] uses scalar borders 2,2; [30] uses $2\mathbf1_{10}$ on each side; [31] uses $a=(17/8,2,\ldots,2)^T$, $b=(21/10,2,\ldots,2)^T$, each with ten entries. In the following table each entry c means that the corresponding criterion strictly detects entanglement for every $c\le p\le1$:
--
--   $$\begin{array}{c|ccccc}t&[18]&[29]&[30]&[31]&\text{our theorem}\\hline0.2&0.9955&0.9943&0.99408&0.99406&0.994043\0.4&0.9960&0.9948&0.99463&0.99462&0.994607\0.6&0.9972&0.9964&0.99627&0.99626&0.996251\0.8&0.9986&0.9982&0.998127&0.998125&0.9981233\0.9&0.9993&0.9991&0.99906893&0.99906843&0.999067726\end{array}.$$
--
--   Thus $\rho_p$ is entangled throughout each indicated interval, and in each of these five rows our sufficient cutoff is strictly smaller than all four earlier cutoffs. This is a finite comparison, not a dominance theorem for arbitrary states or parameters.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 5, Example 2 (begins p.4) and Table II

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF pp.4--5, Example 2 and ALL five rows and columns of Table II:
strict detection on the printed sufficient intervals, plus the smaller new cutoff.
This finite table is not a uniform comparison over arbitrary states. -/
theorem whiteNoiseBoundEntangled33Detection (row column : Fin 5) (p : ℝ)
    (hp : exampleTwoCutoff row column ≤ p) (hpOne : p ≤ 1) :
    (0 < bipartiteViolation (exampleTwoChoice column)
      (exampleTwoState (exampleTwoParameter row) p) ∧
      ¬ Entanglement.IsSeparableDensity (exampleTwoState (exampleTwoParameter row) p)) ∧
    (∀ old : Fin 4, exampleTwoCutoff row 4 < exampleTwoCutoff row old.castSucc) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
