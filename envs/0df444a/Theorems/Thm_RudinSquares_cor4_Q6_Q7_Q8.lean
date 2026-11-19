-- Prove2me | Theorems.Thm_RudinSquares_cor4_Q6_Q7_Q8
-- name    : RudinSquares.cor4_Q6_Q7_Q8
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:23:13.438316+00:00
-- url     : https://prove2.me/theorems/e75d4b31-01df-4c6d-b061-3ec30f5c0d98
-- title:
--   Corollary 4 — $Q(6)=Q(7)=4$ and $Q(8)=5$
-- statement:
--   Corollary 4 of the paper. The maximal number of squares in the first $N$ terms of a non-trivial integer arithmetic progression satisfies
--   $$Q(6)=Q(7)=4,\qquad Q(8)=5.$$
--   This follows from Proposition 3 by a short case analysis on five-element subsets, together with the progression $24n+1$, which has five squares among its first eight terms (at positions $0,1,2,5,7$). It is the starting point of the recursion that determines $Q(N)$ up to $N=52$.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, Corollary 4, p. 60.

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem cor4_Q6_Q7_Q8 : Q 6 = 4 ∧ Q 7 = 4 ∧ Q 8 = 5 := by sorry
end RudinSquares
