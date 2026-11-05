-- Prove2me | Theorems.Thm_StrongConv_tendsto_prob_norm_adjPerp_ge_highDegree
-- name    : StrongConv.tendsto_prob_norm_adjPerp_ge_highDegree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:54:12.360212+00:00
-- url     : https://prove2.me/theorems/d01fc379-480b-4cfe-9256-c4c7fcc26098
-- title:
--   Brailovskaya–van Handel, Remark 3.9 — the high-degree lower bound ‖Aᴺ‖ ≥ (1 − o(1))·2√(2d−1)
-- statement:
--   Let $d : \mathbb N \to \mathbb N$ satisfy $d(N)/(\log N)^4 \to \infty$. For every $\delta > 0$,
--   $$\mathbf P\big[\|A^N\| \ge (1 - \delta)\,2\sqrt{2d(N)-1}\big] \to 1 \quad (N \to \infty),$$
--   where $A^N$ is the adjacency matrix of the random $2d(N)$-regular graph on $N$ vertices (permutation model) restricted to $\{1_N\}^\perp$. No upper bound on the growth of $d(N)$ is assumed, so $d(N)$ may be a power of $N$ or larger.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 10, the high-degree lower bound behind the proof of Corollary 3.5, which cites Brailovskaya, T. and van Handel, R., Universality and sharp matrix concentration inequalities, Geom. Funct. Anal. 34 (2024) 1734–1838, https://doi.org/10.1007/s00039-024-00692-9, §3.2.2, Remark 3.9

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology

namespace StrongConv

theorem tendsto_prob_norm_adjPerp_ge_highDegree (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / Real.log N ^ 4) atTop atTop) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      (1 - δ) * (2 * Real.sqrt (2 * d N - 1)) ≤ ‖adjPerp σ‖)) atTop (𝓝 1) := by
  sorry

end StrongConv
