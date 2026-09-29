-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model
-- name    : WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d439f6e7-8f94-5d50-843c-e6b0444e5bf0
-- title:
--   The points (0,y) on y²=x³+B are flexes
-- statement:
--   Let $k$ be a field with decidable equality, let $B \in k$, and assume $2 \neq 0$ in $k$. Let $y \in k$ be nonzero, and suppose $(0,y)$ is a nonsingular point of the affine Weierstrass curve with coefficients $a_1 = a_2 = a_3 = a_4 = 0$ and $a_6 = B$, i.e. of $y^2 = x^3 + B$; here `Nonsingular` means that the Weierstrass equation holds at $(0,y)$ and that the two partial derivatives of the defining polynomial do not both vanish there. Writing $P$ for the corresponding element `Point.some 0 y h` of the group of points of this affine curve (rational points together with the point at infinity), the assertion is $P + P = -P$ in that group. Equivalently, $P$ is a point of order dividing three, although the statement is phrased purely as the displayed identity between the double of $P$ and the negative of $P$, not as a torsion statement.
--
--   This is the classical fact that the points with $x = 0$ on a curve $y^2 = x^3 + B$ are inflection points, hence three-torsion: the tangent there is horizontal and meets the curve at the same point again. It is used in the analysis of the three-torsion and of the action of the cube-root-of-unity automorphism on curves with $j = 0$, in particular by [`WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three`](thm.html#WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three) and the two counting statements [`WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree`](thm.html#WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree) and its variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by sorry
