-- Prove2me | Theorems.Thm_StrongConv_tendsto_prob_abs_norm_schreierAdjPerp_sub_le
-- name    : StrongConv.tendsto_prob_abs_norm_schreierAdjPerp_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:54.51014+00:00
-- url     : https://prove2.me/theorems/63d66a27-8d2b-4720-a982-b9dba100aca1
-- title:
--   Schreier graphs on k-tuples — the second eigenvalue is 2√(2d−1) + o(1) with probability 1 − o(1)
-- statement:
--   Fix $d \ge 2$ and $k \ge 1$, and let $\sigma_1, \dots, \sigma_d$ be i.i.d. uniform elements of $\mathbf S_N$. Let $A^N$ (`schreierAdjPerp k σ`) be the adjacency matrix of the $2d$-regular Schreier graph of the action of $\mathbf S_N$ on $k$-tuples of distinct elements of $\{1, \dots, N\}$ defined by $\sigma_1, \dots, \sigma_d$, restricted to the orthogonal complement $\{1\}^\perp$ of the all-ones vector (see the milestone on the restricted adjacency matrix for the definitions). Then for every $\delta > 0$
--   $$\mathbf P\Big[\big|\|A^N\| - 2\sqrt{2d-1}\big| \le \delta\Big] \to 1 \qquad (N \to \infty).$$
--   That is, $\|A^N\| = 2\sqrt{2d-1} + o(1)$ with probability $1 - o(1)$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 14, the second eigenvalue of random Schreier graphs on k-tuples

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG2

open Filter Topology

namespace StrongConv

theorem tendsto_prob_abs_norm_schreierAdjPerp_sub_le (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      |‖schreierAdjPerp k σ‖ - 2 * Real.sqrt (2 * d - 1)| ≤ δ)) atTop (𝓝 1) := by
  sorry

end StrongConv
