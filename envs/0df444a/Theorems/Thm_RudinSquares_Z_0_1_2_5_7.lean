-- Prove2me | Theorems.Thm_RudinSquares_Z_0_1_2_5_7
-- name    : RudinSquares.Z_0_1_2_5_7
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:24:42.667087+00:00
-- url     : https://prove2.me/theorems/dfbcab0b-0f4a-4bb9-8db3-65c72ebf4e3b
-- title:
--   Section 4.1 — $Z_I=\{(24,1)\}$ for $I={0,1,2,5,7}$
-- statement:
--   A computation from Section 4.1. For the five-element index set $I={0,1,2,5,7}$, the set of squarefree-gcd non-trivial progressions that are square at every position of $I$ is exactly
--   $$Z_I=\{(24,1)\}.$$
--   In particular $z_I$ equals the number of listed pairs. The case $I=\{0,1,2,5,7\}$ is the Rudin sequence itself: the unique progression is $24n+1$, whose square positions are $0,1,2,5,7$. These explicit determinations of $Z_I$ feed the recursion proving Theorem 1 and identify the extremal progressions in Table 4.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, §4.1, pp. 70–71 (case $I={0,1,2,5,7}$).

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem Z_0_1_2_5_7 : Zset ({0,1,2,5,7} : Finset ℤ) = ({(24, 1)} : Set (ℤ × ℤ)) := by sorry
end RudinSquares
