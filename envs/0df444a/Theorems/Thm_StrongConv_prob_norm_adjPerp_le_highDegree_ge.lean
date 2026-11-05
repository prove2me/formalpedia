-- Prove2me | Theorems.Thm_StrongConv_prob_norm_adjPerp_le_highDegree_ge
-- name    : StrongConv.prob_norm_adjPerp_le_highDegree_ge
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T22:53:23.261212+00:00
-- url     : https://prove2.me/theorems/80c880a0-cb1c-41f9-abec-c16af0a386b5
-- title:
--   Brailovskaya–van Handel, Theorem 3.8 — random regular graphs of high degree are nearly Ramanujan
-- statement:
--   For every $a > 0$ there is $C > 0$ such that for all $N, d \ge 1$, with probability at least $1 - N^{-a}$,
--   $$\|A^N\| \le \Big(1 + C\frac{(\log N)^{3/4}}{N^{1/4}} + C\frac{(\log N)^{2/3}}{d^{1/6}} + C\frac{\log N}{d^{1/2}}\Big)2\sqrt{2d},$$
--   where $A^N$ is the adjacency matrix of the random $2d$-regular graph on $N$ vertices (permutation model) restricted to $\{1_N\}^\perp$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 10, the high-degree bound cited in the proof of Corollary 3.5, which cites Brailovskaya, T. and van Handel, R., Universality and sharp matrix concentration inequalities, Geom. Funct. Anal. 34 (2024) 1734–1838, https://doi.org/10.1007/s00039-024-00692-9, §3.2.2, Theorem 3.8

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem prob_norm_adjPerp_le_highDegree_ge (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      1 - (N : ℝ) ^ (-a) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖adjPerp σ‖ ≤ (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))) := by
  sorry

end StrongConv
