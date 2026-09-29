-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one
-- name    : WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e940c092-8bae-5df8-a824-04ad1216a8fb
-- title:
--   Collinear points (x,y),(ω x,y),(ω² x,y) on y²=x³+B
-- statement:
--   Let $k$ be a field with decidable equality, let $B,\omega \in k$, and consider the Weierstrass curve over $k$ with coefficients $a_1=a_2=a_3=a_4=0$ and $a_6=B$, i.e. $y^2 = x^3 + B$, viewed in its affine model. Assume $\omega^3 = 1$ and $\omega \neq 1$, so that $\omega$ is a primitive cube root of unity. Let $x,y \in k$ and assume that each of the three pairs $(x,y)$, $(\omega x, y)$ and $(\omega^2 x, y)$ satisfies Mathlib's `Nonsingular` predicate for this affine curve (lying on the curve, with the two partial derivatives of the Weierstrass polynomial not both vanishing), and assume $x \neq 0$. Then, in the group of affine points of the curve, the sum of the points $(x,y)$ and $(\omega x, y)$ equals the negative of the point $(\omega^2 x, y)$; equivalently, the three points add up to the point at infinity. The three nonsingularity hypotheses are taken as separate assumptions, although the second and third are consequences of the first.
--
--   This is the statement that the horizontal line $Y = y$ cuts the curve $y^2 = x^3 + B$ in the three points whose $x$-coordinates are $x$, $\omega x$, $\omega^2 x$, and that three collinear points sum to zero; in endomorphism terms it is the relation $1 + [\omega] + [\omega^2] = 0$ for the order-three automorphism $(x,y) \mapsto (\omega x, y)$ of a curve with $j = 0$. It is used in the analysis of the three-torsion and of the automorphism of order three on such curves, in [`WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three`](thm.html#WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three) and in the two counting statements [`WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree`](thm.html#WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree) and its variant for nonzero argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one
    {k : Type*} [Field k] [DecidableEq k] (B w : k) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) {x y : k}
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
    (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
    (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y) (hx : x ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by sorry
