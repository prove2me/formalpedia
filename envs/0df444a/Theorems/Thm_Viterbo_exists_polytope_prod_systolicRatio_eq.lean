-- Prove2me | Theorems.Thm_Viterbo_exists_polytope_prod_systolicRatio_eq
-- name    : Viterbo.exists_polytope_prod_systolicRatio_eq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:17:28.937171+00:00
-- url     : https://prove2.me/theorems/ae499a0e-73bc-4fa4-ac16-7394dae8dcc2
-- title:
--   §1.1(ii) — in every ℝ²ⁿ a Lagrangian product of convex polytopes has systolic ratio ((√5 + 3)/5)^⌊n/2⌋
-- statement:
--   For every $n \ge 1$ there are convex polytopes $K_n, T_n \subset \mathbb R^n$ (convex hulls of finite sets, with nonempty interior) whose Lagrangian product $K_n \times T_n \subset \mathbb R^{2n}$ has $\mathrm{Sys}(K_n \times T_n) = \big(\frac{\sqrt5 + 3}{5}\big)^{\lfloor n/2\rfloor}$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), pp. 6–7, the polytope counterexamples of §1.1(ii)

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem exists_polytope_prod_systolicRatio_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ K T : Set (OAI.SymmetricPolar.Position n),
      (∃ s : Finset (OAI.SymmetricPolar.Position n), K = convexHull ℝ (s : Set _)) ∧
      (∃ s : Finset (OAI.SymmetricPolar.Position n), T = convexHull ℝ (s : Set _)) ∧
      IsConvexDomain K ∧ IsConvexDomain T ∧
      systolicRatio (K ×ˢ T) = ENNReal.ofReal (((Real.sqrt 5 + 3) / 5) ^ (n / 2)) := by
  sorry

end Viterbo
