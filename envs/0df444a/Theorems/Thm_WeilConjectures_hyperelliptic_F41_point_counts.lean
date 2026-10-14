-- Prove2me | Theorems.Thm_WeilConjectures_hyperelliptic_F41_point_counts
-- name    : WeilConjectures.hyperelliptic_F41_point_counts
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T14:59:00.363303+00:00
-- url     : https://prove2.me/theorems/ab0d1621-785a-4749-8b0a-3b43b3055b07
-- title:
--   $y^2+y=x^5$ over $\mathbb F_{41}$: $N_1=33$, $N_2=1743$
-- statement:
--   Consider the genus-2 hyperelliptic curve $C: y^2+y=x^5$ over $\mathbb F_{41}$. Counting affine solutions $(x,y)$ over $\mathbb F_{41}$ and $\mathbb F_{41^2}$ and adding one point at infinity gives
--
--   $$N_1=\#\{(x,y)\in\mathbb F_{41}^2: y^2+y=x^5\}+1=33,\qquad N_2=\#\{(x,y)\in\mathbb F_{41^2}^2: y^2+y=x^5\}+1=1743.$$
--
--   These counts determine the coefficients $c_1=N_1-1-q=-9$ and $c_2=(N_2-1-q^2+c_1^2)/2=71$ of the Weil polynomial $P_1$.
--
--   **Formalization Note** $\mathbb F_{41}$ is `ZMod 41` and $\mathbb F_{41^2}$ is `GaloisField 41 2`; the primality of 41 is supplied as a `Fact` instance argument.
-- source:
--   Wikipedia, "Weil conjectures", https://en.wikipedia.org/wiki/Weil_conjectures (PDF snapshot supplied by the proposer, 14 pp.), section "Examples", subsection "Hyperelliptic curves" (counting yields $N_1=33$ and $N_2=1743$)

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial

namespace WeilConjectures

theorem hyperelliptic_F41_point_counts [Fact (Nat.Prime 41)] :
    Nat.card {xy : ZMod 41 × ZMod 41 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1 = 33 ∧
    Nat.card {xy : GaloisField 41 2 × GaloisField 41 2 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1 = 1743 := by sorry

end WeilConjectures
