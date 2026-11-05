-- Prove2me | Theorems.Thm_StrongConv_norm_adjPerp_ge_alonBoppana
-- name    : StrongConv.norm_adjPerp_ge_alonBoppana
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:53:47.918335+00:00
-- url     : https://prove2.me/theorems/5db8e057-9a4d-4b81-821b-d563deb5668b
-- title:
--   Alon–Boppana bound for the random regular graph — ‖Aᴺ‖ ≥ (1 − C log 2d / log N)·2√(2d−1)
-- statement:
--   There is a universal constant $C$ such that for all $d \ge 1$, $N \ge 2$ and every $d$-tuple of permutations of $\{1, \dots, N\}$,
--   $$\|A^N\| \ge \Big(1 - C\frac{\log 2d}{\log N}\Big)2\sqrt{2d-1},$$
--   where $A^N = \sum_i (S_i^N + S_i^{N*})$ is the adjacency matrix of the corresponding $2d$-regular multigraph (loops and multiple edges allowed) restricted to $\{1_N\}^\perp$. The statement is deterministic: it holds for every tuple, not only with high probability.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 10, the Alon–Boppana bound cited in the proof of Corollary 3.5, which cites Nilli, A., On the second eigenvalue of a graph, Discrete Math. 91 (1991) 207–210, https://doi.org/10.1016/0012-365X(91)90112-F, in the uniform form of Brailovskaya, T. and van Handel, R., Universality and sharp matrix concentration inequalities, Geom. Funct. Anal. 34 (2024) 1734–1838, https://doi.org/10.1007/s00039-024-00692-9, Lemma 3.7

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem norm_adjPerp_ge_alonBoppana :
    ∃ C : ℝ, ∀ d N : ℕ, 1 ≤ d → 2 ≤ N → ∀ σ : Fin d → Equiv.Perm (Fin N),
      (1 - C * Real.log (2 * d) / Real.log N) * (2 * Real.sqrt (2 * d - 1)) ≤ ‖adjPerp σ‖ := by
  sorry

end StrongConv
