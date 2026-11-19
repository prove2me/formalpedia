-- Prove2me | Theorems.Thm_RudinSquares_z_0_1_4_7_8
-- name    : RudinSquares.z_0_1_4_7_8
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:25:40.880743+00:00
-- url     : https://prove2.me/theorems/2a7293c1-5d97-4038-ac33-6f35d5d49b6d
-- title:
--   Section 4.1 — $z_I=0$ for $I={0,1,4,7,8}$
-- statement:
--   A computation from Section 4.1 (the elliptic-curve Chabauty algorithm at work). For the five-element index set $I={0,1,4,7,8}$, the set $Z_I$ is empty, i.e. $z_I=0$: there is no non-trivial integer arithmetic progression with squarefree $\gcd(q,a)$ that is a square at every position of $I$. The paper proves this by exhibiting a genus-1 quotient cover for which every relevant twist has no rational point (or only points giving trivial points of $C_I$). Such vanishings are the sieve steps that force $Q(N+1)=Q(N)$ in the recursion.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, §4.1, pp. 69–71 (case $I={0,1,4,7,8}$).

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem z_0_1_4_7_8 : z ({0,1,4,7,8} : Finset ℤ) = 0 := by sorry
end RudinSquares
