-- Prove2me | Theorems.Thm_TensorNP_SymEigen_theorem_9_2
-- name    : TensorNP.SymEigen.theorem_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:36.169125+00:00
-- url     : https://prove2.me/theorems/13f5b198-530c-4f4a-9eac-07f569c1ab44
-- title:
--   Theorem 9.2 (Nesterov) — √(1 − 1/α(G)) = 3√(3/2) · max over the unit sphere of Σ_{i<j, {i,j}∉E} x_i x_j y_ij
-- statement:
--   Let $G=(V,E)$ be a simple graph on $v\ge1$ vertices with stability number $\alpha(G)$, the largest size of a set of pairwise non-adjacent vertices. Let $n=v+v(v-1)/2$ and
--   $$\mathbb S^{n-1}=\{(\mathbf x,\mathbf y)\in\mathbb R^v\times\mathbb R^{v(v-1)/2}:\ \|\mathbf x\|_2^2+\|\mathbf y\|_2^2=1\}.$$
--   Then the maximum of Nesterov's cubic over $\mathbb S^{n-1}$ exists, and
--   $$\sqrt{1-\frac1{\alpha(G)}}=3\sqrt{\frac32}\cdot\max_{(\mathbf x,\mathbf y)\in\mathbb S^{n-1}}\ \sum_{i<j,\ \{i,j\}\notin E}x_ix_jy_{ij}.$$
--
--   This is Nesterov's characterization of the stability number by a cubic optimization problem over the sphere, with the factor $1/\sqrt2$ that Hillar and Lim point out is missing from Nesterov's original statement (their footnote 12). It is the bridge from the combinatorial quantity $\alpha(G)$ to the largest eigenvalue of the tensor $\mathcal S_G$.
--
--   **Formalization Note** The maximum is stated as the greatest element of the set of values, so its attainment is part of the claim. The hypothesis $v\ge1$ is the paper's standing setting ($\alpha(G)\in\{1,\dots,v\}$); for $v=0$ the sphere is empty.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:27, Theorem 9.2 (Nesterov), (31), and footnote 12

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace TensorNP.SymEigen

theorem theorem_9_2 {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    ∃ M : ℝ,
      IsGreatest {t : ℝ | ∃ (x : Fin v → ℝ) (y : PairIdx v → ℝ),
          ∑ i, x i ^ 2 + ∑ p, y p ^ 2 = 1 ∧ t = nesterovForm G x y} M ∧
        Real.sqrt (1 - 1 / (G.indepNum : ℝ)) = 3 * Real.sqrt (3 / 2) * M := by sorry

end TensorNP.SymEigen
