-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_weyl_geometric_seed_efficient
-- name    : QAlgorithms.Papers.Independent.Support21.P09.weyl_geometric_seed_efficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:50:51.958559+00:00
-- url     : https://prove2.me/theorems/18a1918a-b57b-4b1d-a708-70860821cdf6
-- title:
--   Efficient exact geometric-seed Weyl POVMs
-- statement:
--   There is one polynomial $p\in\mathbb N[x]$ such that the following holds for every $k\ge2$ and $a\in\mathbb C$, including $a=0$. Put $m=2^k$ and
--
--   $$
--   \kappa=2m\sum_{t=0}^{m/2-1}|a|^{2t},\qquad v_j=\frac{a^{\min(j,m-1-j)}}{\sqrt\kappa}\quad(0\le j<m).
--   $$
--
--   Then $\kappa>0$ and $\sum_j|v_j|^2=1/m$. For $t\ge0$, set
--
--   $$
--   B_t=\frac1{\sqrt{1+|a|^{2t}}}\begin{pmatrix}1&a^t\\overline{a^t}&-1\end{pmatrix},\qquad B=B_{m/4}\otimes B_{m/8}\otimes\cdots\otimes B_1\otimes B_0.
--   $$
--
--   Let the column-action permutation $J$ send $2i$ to $i$ for $0\le i<m/2$ and $2i-1$ to $m-i$ for $1\le i\le m/2$. The corrected completion
--
--   $$
--   A=JBJ^\dagger F_m^\dagger
--   $$
--
--   is unitary with first row $\sqrt m\,v^T F_m^\dagger$. With $Z=\bigoplus_jT^{-j}$, the unitary $D=(F_m\otimes F_m^\dagger)Z(A^\dagger\otimes I_m)$ exactly implements the $m^2$ labeled column effects of $T^lS^jv$ on $|0\rangle\langle0|\otimes\rho$, for every density matrix $\rho$. It has an exact circuit on $2k$ qubits of at most $p(k)$ arbitrary elementary one- and two-qubit unitary gates.
--
--   The printed order $J^\dagger BJ$ is corrected to $JBJ^\dagger$ for the printed column action of $J$: at $m=4$ only the latter gives the required reflected row $(1,a,a,1)$. No numerical joint-localization error bound is asserted.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 20, §6.3: efficient geometric-seed Weyl POVMs

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.20–21, Eq.(4), Figures 2–3: an efficient exact geometric-seed Weyl POVM,
uniformly over complex alpha, including alpha=0. Correct the printed J^dagger B J to
J B J^dagger for the paper's column-action permutation: at m=4 the printed order yields
(1,alpha,1,alpha), whereas Eq.(4) requires (1,alpha,alpha,1). The lower-left entry of
B_t is conjugated, and the final factor is B_0. Independent moderation of this source
correction remains required. -/
theorem weyl_geometric_seed_efficient :
    ∃ p : Polynomial ℕ, ∀ k : ℕ, 2 ≤ k → ∀ a : ℂ,
      let m := 2 ^ k
      let v := geometricSeed m a
      let A := geometricA k a
      0 < geometricKappa m a ∧
      (∑ r, ‖v r‖ ^ 2) = 1 / (m : ℝ) ∧
      A ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
      (∀ j, A 0 j = weylRow m v j) ∧
      RankOnePOVM (weylColumns m v) ∧
      ImplementsPOVM (weylColumns m v) (weylD m A) (fun r => (0, r)) ∧
      ∃ circ : Circuit elementaryGates (k + k), circ.size ≤ p.eval k ∧
        circ.unitary = (weylD m A).submatrix
          (registerIndex k k) (registerIndex k k) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
