-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero_of_not_isElliptic
-- name    : WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero_of_not_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/a52fe414-bd9a-5d19-80f7-1d189a06cb82
-- title:
--   Integrality of torsion coordinates on a non-elliptic Weierstrass curve
-- statement:
--   Let $F$ be a field of characteristic zero, $L$ a field equipped with an $F$-algebra structure, and $W$ a Weierstrass curve over $F$ which is not elliptic, i.e. whose discriminant fails to be a unit. Let $n$ be an integer whose image in $F$ is nonzero, and let $x, y \in L$ be such that the pair $(x,y)$ is a nonsingular point of the affine curve $W\!\cdot\!{\otimes}\,L$ obtained from $W$ by base change along $F \to L$: it satisfies the Weierstrass equation and at least one of the two partial derivatives of the Weierstrass polynomial does not vanish there. Assume that the corresponding point `some x y hns` of the group of affine points of the base-changed curve, formed by the chord–tangent law, is killed by $n$, that is $n \cdot (x,y) = 0$. Then both $x$ and $y$ are integral over $F$, i.e. each is a root of a monic polynomial with coefficients in $F$.
--
--   This is the statement that coordinates of torsion points on the smooth locus are integral over the field of definition, in the case of a Weierstrass curve with vanishing discriminant; together with its counterpart for elliptic curves it covers arbitrary Weierstrass curves. It is used in the comparison of $n$-torsion under the maps of points of a non-elliptic Weierstrass curve between algebraic closures of $\mathbb{Q}$ and of $\mathbb{Q}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero_of_not_isElliptic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in

theorem WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero_of_not_isElliptic
    {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {W : WeierstrassCurve F} (hW : ¬ W.IsElliptic) [CharZero F] {n : ℤ} (hn : (n : F) ≠ 0)
    {x y : L} (hns : (W⁄L).Nonsingular x y)
    (hQ : n • (WeierstrassCurve.Affine.Point.some x y hns : (W⁄L).Point) = 0) :
    _root_.IsIntegral F x ∧ _root_.IsIntegral F y := by sorry
