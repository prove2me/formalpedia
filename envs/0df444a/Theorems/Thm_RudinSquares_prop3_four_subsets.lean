-- Prove2me | Theorems.Thm_RudinSquares_prop3_four_subsets
-- name    : RudinSquares.prop3_four_subsets
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:22:39.153372+00:00
-- url     : https://prove2.me/theorems/2bde47b6-46b1-444b-bb05-278b46eb57d6
-- title:
--   Proposition 3 — four-element index sets in $\{0,\dots,6\}$ with $z_I=0$
-- statement:
--   Proposition 3 of the paper. Let $I$ be a four-element subset of $\{0,1,\dots,6\}$. Then $z_I=\infty$ unless $I$ is equivalent (under integer translation and rational dilation) to one of the five sets
--   $$\{0,1,2,3\},\ \{0,1,3,4\},\ \{0,1,4,5\},\ \{0,2,3,5\},\ \{0,1,5,6\},$$
--   in which case $z_I=0$. Equivalently: if $I$ is equivalent to one of these five sets then $Z_I$ is empty; otherwise $Z_I$ is infinite. The five exceptional sets are exactly the symmetric four-term patterns whose associated elliptic curve has rank $0$ and only the eight trivial rational points. This is the base case of the sieve used to bound $Q(N)$ for small $N$.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, Proposition 3, p. 60.

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem prop3_four_subsets (I : Finset ℤ) (hI : I ⊆ Finset.Icc (0 : ℤ) 6) (hcard : I.card = 4) :
    (GenEq I {0,1,2,3} ∨ GenEq I {0,1,3,4} ∨ GenEq I {0,1,4,5} ∨ GenEq I {0,2,3,5} ∨ GenEq I {0,1,5,6} → z I = 0) ∧
    (¬ (GenEq I {0,1,2,3} ∨ GenEq I {0,1,3,4} ∨ GenEq I {0,1,4,5} ∨ GenEq I {0,2,3,5} ∨ GenEq I {0,1,5,6}) → z I = ⊤) := by sorry
end RudinSquares
