-- Prove2me | Theorems.Thm_RudinSquares_Z_0_13_24_33_49
-- name    : RudinSquares.Z_0_13_24_33_49
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:26:09.224624+00:00
-- url     : https://prove2.me/theorems/33eed11b-6c5a-4118-a642-ef036c4df6ee
-- title:
--   Section 4.1 — $Z_I=\{(24,49),(-1,49)\}$ for $I={0,13,24,33,49}$
-- statement:
--   A computation from Section 4.1. For the five-element index set $I={0,13,24,33,49}$, the set of squarefree-gcd non-trivial progressions that are square at every position of $I$ is exactly
--   $$Z_I=\{(24,49),(-1,49)\}.$$
--   In particular $z_I$ equals the number of listed pairs. The case $I=\{0,1,2,5,7\}$ is the Rudin sequence itself: the unique progression is $24n+1$, whose square positions are $0,1,2,5,7$. These explicit determinations of $Z_I$ feed the recursion proving Theorem 1 and identify the extremal progressions in Table 4.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, §4.1, pp. 70–71 (case $I={0,13,24,33,49}$).

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem Z_0_13_24_33_49 : Zset ({0,13,24,33,49} : Finset ℤ) = ({(24, 49), (-1, 49)} : Set (ℤ × ℤ)) := by sorry
end RudinSquares
