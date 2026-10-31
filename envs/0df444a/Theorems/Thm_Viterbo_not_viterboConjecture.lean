-- Prove2me | Theorems.Thm_Viterbo_not_viterboConjecture
-- name    : Viterbo.not_viterboConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T09:38:47.129712+00:00
-- url     : https://prove2.me/theorems/c55c63a6-faa6-4168-9896-65cdcdca61b9
-- title:
--   Theorem 1.3 — Viterbo's conjecture fails for every n ≥ 2
-- statement:
--   For every $n \ge 2$, Viterbo's volume-capacity conjecture in $\mathbb R^{2n}$ is false: it is not the case that $c(K)^n \le n!\,\mathrm{Vol}(K)$ for every symplectic capacity $c$ (Definition 1.1) and every convex domain $K \subset \mathbb R^{2n}$.
--
--   Haim-Kislev–Ostrover, p. 3: “**Theorem 1.3.** *Viterbo’s conjecture fails for every $n \ge 2$.*”
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 3, Theorem 1.3

import Mathlib
import Definitions.Def_Viterbo

namespace Viterbo

theorem not_viterboConjecture (n : ℕ) (hn : 2 ≤ n) : ¬ ViterboConjecture n := by
  sorry

end Viterbo
