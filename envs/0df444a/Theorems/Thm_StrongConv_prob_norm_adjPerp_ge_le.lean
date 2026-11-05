-- Prove2me | Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_le
-- name    : StrongConv.prob_norm_adjPerp_ge_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:52:57.360547+00:00
-- url     : https://prove2.me/theorems/55b5b8c0-8844-4269-a6c6-1f68c0956ba2
-- title:
--   Theorem 3.4 — an effective Friedman theorem
-- statement:
--   There is a universal constant $C$ such that for all $d \ge 2$, $N \ge 1$ and $0 < \varepsilon < 2d - 2\sqrt{2d-1}$,
--   $$\mathbf P\big[\|A^N\| \ge 2\sqrt{2d-1} + \varepsilon\big] \le C\,\frac1N\Big(\frac{d\log d}{\varepsilon}\Big)^8\log\Big(\frac{2ed}{\varepsilon}\Big),$$
--   where $A^N = S_1^N + S_1^{N*} + \cdots + S_d^N + S_d^{N*}$ is the adjacency matrix of the random $2d$-regular graph on $N$ vertices (permutation model, $d$ i.i.d. uniform permutations) restricted to $\{1_N\}^\perp$. The paper's $\lesssim$ is read as a universal constant, and $\varepsilon > 0$ is read in: the bound is undefined for $\varepsilon \le 0$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 9, Theorem 3.4 (an effective Friedman theorem)

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem prob_norm_adjPerp_ge_le :
    ∃ C : ℝ, ∀ d N : ℕ, 2 ≤ d → 1 ≤ N → ∀ ε : ℝ, 0 < ε →
      ε < 2 * d - 2 * Real.sqrt (2 * d - 1) →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖) ≤
        C * (1 / N) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε) := by
  sorry

end StrongConv
