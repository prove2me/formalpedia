-- Prove2me | Theorems.Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet
-- name    : WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/99841a34-31c0-570f-ae9f-f8802f859369
-- title:
--   Vélu's formulas land on the quotient curve (odd order)
-- statement:
--   Let $L$ be an algebraically closed field in which $2 \neq 0$, and let $W$ be a Weierstrass curve over $L$ with invertible discriminant. Let $n$ be a natural number and let $Q$ be an affine point of $W$ whose additive order equals $2n+1$. Put $S = W.\mathrm{oddOrderSummingSet}\,Q\,n$, the finite subset of $L \times L$ obtained as the image of $\{1,\dots,n\}$ under $k \mapsto$ the coordinate pair of $k \cdot Q$ (the point at infinity being sent to $(0,0)$). For $P = (x_P,y_P)$ write $g^x_P = 3x_P^2 + 2a_2x_P + a_4 - a_1y_P$, $g^y_P = -(2y_P + a_1x_P + a_3)$, $t_P = 2g^x_P - a_1g^y_P$, $u_P = (g^y_P)^2$, and let $t = \sum_{P \in S} t_P$, $w = \sum_{P \in S} W.\mathrm{veluW}\,x_P\,y_P$. Then for any $x, y \in L$ satisfying the affine Weierstrass equation of $W$ and such that $x \neq x_P$ for every $P \in S$, the pair $\bigl(\mathrm{veluX}_S(x), \mathrm{veluY}_S(x,y)\bigr)$, given by the Vélu sums $x + \sum_{P}\bigl(t_P/(x-x_P) + u_P/(x-x_P)^2\bigr)$ and $y - \sum_P\bigl(u_P(2y+a_1x+a_3)/(x-x_P)^3 + t_P(a_1(x-x_P)+y-y_P)/(x-x_P)^2 + (a_1u_P - g^x_Pg^y_P)/(x-x_P)^2\bigr)$, satisfies the affine Weierstrass equation of the curve with coefficients $a_1, a_2, a_3$, $a_4 - 5t$, $a_6 - b_2 t - 7w$.
--
--   This is the part of Vélu's Théorème 1 asserting that the explicit coordinate maps attached to a summing set for the odd cyclic subgroup $\langle Q \rangle$ carry affine points of $W$ (away from the kernel abscissae) to points of the quotient curve; the group-homomorphism properties are treated separately. It is used in the construction of the Vélu isogeny at the level of function fields and in the comparison of $2$-division values on $W$ and on the quotient curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) := by sorry
