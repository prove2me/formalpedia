-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_region0_utility_increases
-- name    : ProblemSpec.Equilibrium.region0_utility_increases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:29.960339+00:00
-- url     : https://prove2.me/theorems/902f6777-252b-47e8-a4d7-837bb42f82e6
-- title:
--   App. p. 2, Region 0 — at a fixed N, the entry utility strictly increases with S_r
-- statement:
--   Let $N>1$, $S_g\ge0$ and $0\le S_r<S_r'$, and suppose designers guess at $S_r'$ given $N$ participants, i.e. $S_r'<\bar r^g(N)$ (Region 0). Then
--   $$U(N;S_r)<U(N;S_r'),$$
--   where $U(N;\cdot)$ is a participant's expected utility when all $N$ participants play $(r^*(N),m^*(N))$.
--
--   In Region 0 the number of incorporated objectives $r^*=\bar r^g(N)$ does not move with $S_r$, and every disclosed objective replaces a guessed one, which is cheaper since $c_1<c_g$. This is the step behind "$N^*$ increases with $S_r$ where designers guess".
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 2 (PDF 30), 'Region 0: the number of participants increases with more disclosed conceptual objectives'

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- Region 0, App. p. 2 (PDF 30): "under the same level of participation, the designer's total
participation cost is lower as more objectives are disclosed, since `cg > c1` and `r∗` does not
change with `Sr` in Region 0 (under the same `N`). Consequently, designers' expected utilities
increase with `Sr` (given the same `N`)." For `N > 1` and `0 ≤ Sr < Sr'` with designers guessing
at `Sr'` (`Sr' < r̄^g(N)`), the equilibrium expected utility at `Sr'` strictly exceeds that at
`Sr`. -/
theorem region0_utility_increases (P : Params) (hP : P.Standing) (Sr Sr' Sg N : ℝ)
    (hSr : 0 ≤ Sr) (hlt : Sr < Sr') (hSg : 0 ≤ Sg) (hN : 1 < N) (hG : Guessing P N Sr') :
    entryUtility P Sr Sg N < entryUtility P Sr' Sg N := by sorry

end ProblemSpec.Equilibrium
