-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
-- name    : WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/63acd57a-4b5c-5a6d-8d3a-81903d8772f8
-- title:
--   Vélu's isogeny for a cyclic kernel of odd order
-- statement:
--   Let $F$ be an algebraically closed field, $W$ a Weierstrass curve over $F$ which is elliptic, $n$ a natural number with $2n+1$ nonzero in $F$, and $Q$ a point of the affine model `W.toAffine` whose additive order is exactly $2n+1$. Put $S =$ `W.oddOrderSummingSet Q n`, the finite set of pairs obtained by taking, for $1 \le k \le n$, the affine coordinates of $k \bullet Q$ (the point at infinity being sent to $(0,0)$), and let $W/S$ be `W.veluQuotient S`, the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4' = a_4 - 5t$, $a_6' = a_6 - b_2 t - 7w$, where $t = \sum_{P \in S}$ `W.veluT` $P$, with `veluT` $=2g^x - a_1 g^y$, $g^x = 3x^2+2a_2x+a_4-a_1y$, $g^y = -(2y+a_1x+a_3)$, and $w = \sum_{P\in S}$ `W.veluW` $P$. Then there exists an additive group homomorphism $\varphi \colon W(F) \to (W/S)(F)$ between the affine point groups whose kernel is exactly the subgroup of integer multiples of $Q$, and which on every affine point $(x,y)$ (given by a nonsingularity witness) not lying in that subgroup is given by Vélu's formulas, i.e. $\varphi(x,y)$ is the affine point with coordinates `W.veluX S x` and `W.veluY S x y`, namely $x + \sum_{P\in S}\bigl(t_P/(x-x_P) + u_P/(x-x_P)^2\bigr)$ with $u_P = (g^y_P)^2$, and the corresponding expression for the second coordinate.
--
--   This is Vélu's theorem on the quotient of an elliptic curve by a finite subgroup, here in the case of a cyclic kernel $\langle Q \rangle$ of arbitrary odd order $2n+1$ invertible in the base field, rather than of odd prime order: both the shape of the quotient curve and the explicit formulas for the isogeny are recorded, together with the identification of its kernel. It supports the later comparison of homomorphism groups of elliptic curves, the reduction of Vélu quotients over valuation subrings in the lifting arguments, and width computations for places of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (hn : ((2 * n + 1 : ℕ) : F) ≠ 0)
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q n) x)
            (W.veluY (W.oddOrderSummingSet Q n) x y) h') := by sorry
