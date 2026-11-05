-- Prove2me | Theorems.Thm_StrongConv_tendsto_prob_norm_adjPerp_div_sub_one_le
-- name    : StrongConv.tendsto_prob_norm_adjPerp_div_sub_one_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T22:54:34.886252+00:00
-- url     : https://prove2.me/theorems/5a23a2b7-7134-4ed7-9a2b-84f21a007d6f
-- title:
--   Corollary 3.5 — ‖Aᴺ‖ = (1 + o(1))·2√(2d−1) with high probability, for any d = d(N)
-- statement:
--   Let $d : \mathbb N \to \mathbb N$ be any function with $d(N) \ge 1$. For every $\delta > 0$,
--   $$\mathbf P\Big[\Big|\frac{\|A^N\|}{2\sqrt{2d(N)-1}} - 1\Big| \le \delta\Big] \to 1 \quad (N \to \infty),$$
--   where $A^N$ is the adjacency matrix of the random $2d(N)$-regular graph on $N$ vertices (permutation model) restricted to $\{1_N\}^\perp$. That is, $\|A^N\| = (1 + o(1))2\sqrt{2d-1}$ with probability $1 - o(1)$. The paper does not restrict $d(N)$ beyond "arbitrary"; $d(N) \ge 1$ excludes the empty tuple, for which $2\sqrt{2d-1}$ is not defined.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 10, Corollary 3.5

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology

namespace StrongConv

theorem tendsto_prob_norm_adjPerp_div_sub_one_le (d : ℕ → ℕ) (hd : ∀ N, 1 ≤ d N) (δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      |‖adjPerp σ‖ / (2 * Real.sqrt (2 * d N - 1)) - 1| ≤ δ)) atTop (𝓝 1) := by
  sorry

end StrongConv
