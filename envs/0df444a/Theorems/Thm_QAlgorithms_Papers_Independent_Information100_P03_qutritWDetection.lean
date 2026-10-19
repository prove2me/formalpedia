-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P03_qutritWDetection
-- name    : QAlgorithms.Papers.Independent.Information100.P03.qutritWDetection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:34:38.696527+00:00
-- url     : https://prove2.me/theorems/f74044d1-4706-457d-a8d1-e246ab6f5a62
-- title:
--   White-noise qutrit W-state: all Table III intervals
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
--   On $(\mathbb C^3)^{\otimes3}$, define the six-term qutrit state and its white-noise mixture by
--
--   $$\phi_W=\frac{|001\rangle+|010\rangle+|100\rangle+|112\rangle+|121\rangle+|211\rangle}{\sqrt6},\qquad\rho_W^q=(1-q)I_{27}/27+q|\phi_W\rangle\langle\phi_W|.$$
--
--   Our tuple is $P=\left(\begin{smallmatrix}10.65&11.57\11.88&11.94\12.42&11.69\end{smallmatrix}\right)$, $Q=\left(\begin{smallmatrix}12.45&12.81\13.05&12.1\11.62&12.45\end{smallmatrix}\right)$, $\mu=\nu=(1,1)^T/\sqrt2$. The rank-one comparisons use borders $(1,2)^T,(2,1)^T$ for [31], $(1,1)^T,(1,1)^T$ for [30], and scalar borders 1,1 for [22]. The sufficient closed intervals are
--
--   $$\begin{array}{c|c}\text{criterion}&\text{detected interval}\\hline\text{our theorem}&0.804647\le q\le1\[31]&0.805132\le q\le1\[30]&0.805211\le q\le1\[22]&0.805318\le q\le1\end{array}.$$
--
--   Throughout each interval the corresponding score strictly exceeds $M+4/3$ and $\rho_W^q$ is not biseparable, hence genuinely tripartite entangled. The signal fraction q is unrelated to the suffix index in Eq.(16). No exact-root or converse claim is made.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, PDF p. 9, Example 4 and Table III p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF pp.9--10, Example 4 and ALL rows of Table III: strict violation of the
biseparable criterion and genuine tripartite entanglement on sufficient intervals. -/
theorem qutritWDetection (i : Fin 4) (q : ℝ)
    (hq : exampleFourCutoff i ≤ q) (hqOne : q ≤ 1) :
    0 < tripartiteViolation (exampleFourChoice i) (exampleFourState q) ∧
      ¬ IsBiseparable (exampleFourState q) := by sorry

end QAlgorithms.Papers.Independent.Information100.P03

end
