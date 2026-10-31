-- Prove2me | Theorems.Thm_Viterbo_exists_isConvexDomain_gromovWidth_lt_cylindricalCapacity
-- name    : Viterbo.exists_isConvexDomain_gromovWidth_lt_cylindricalCapacity
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:16:56.383367+00:00
-- url     : https://prove2.me/theorems/f4a0cac8-7603-41f5-a7ba-6a5f88cac81d
-- title:
--   §1.1(iii) — the strong Viterbo conjecture fails: c_G(K) < c_Z(K) for some convex domain K ⊂ ℝ²ⁿ, n ≥ 2
-- statement:
--   For every $n \ge 2$ there is a convex domain $K \subset \mathbb R^{2n}$ whose Gromov width is strictly smaller than its cylindrical capacity: $c_G(K) < c_Z(K)$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 7, the failure of the strong Viterbo conjecture

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem exists_isConvexDomain_gromovWidth_lt_cylindricalCapacity (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain K ∧
      OAI.SymmetricPolar.gromovWidth K < cylindricalCapacity K := by
  sorry

end Viterbo
