-- Prove2me | Theorems.Thm_WeierstrassCurve_eq_of_infinite_setOf_equation
-- name    : WeierstrassCurve.eq_of_infinite_setOf_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/d0f0290c-1509-564d-98f3-24f8e600ab75
-- title:
--   Weierstrass models with infinitely many common affine points coincide
-- statement:
--   Let $F$ be a field and let $W$ and $V$ be Weierstrass curves over $F$, i.e. each given by coefficients $a_1,a_2,a_3,a_4,a_6$ in $F$, with no smoothness or non-singularity hypothesis. Consider the set of pairs $(x,y)\in F\times F$ that satisfy the affine Weierstrass equation of $W$ and simultaneously that of $V$, where for a curve with coefficients $a_1,\dots,a_6$ the equation at $(x,y)$ is $y^2+a_1xy+a_3y-(x^3+a_2x^2+a_4x+a_6)=0$ in the sense of Mathlib's `WeierstrassCurve.Affine.Equation`. The hypothesis is that this set of common solutions is infinite as a subset of $F\times F$. The conclusion is that $W=V$ as Weierstrass curves, that is, the two coefficient tuples agree: $a_1=a_1'$, $a_2=a_2'$, $a_3=a_3'$, $a_4=a_4'$ and $a_6=a_6'$. Only affine points with coordinates in $F$ itself are involved; nothing is assumed about the points at infinity or about the discriminants.
--
--   This is the elementary rigidity property of Weierstrass models: the five coefficients of such a model are determined by its affine $F$-points as soon as there are infinitely many of them. It is used in the construction of quotients of elliptic curves by finite subgroups, to pass from an agreement of the coordinate functions of two isogenies with the same kernel to the literal equality of the resulting Weierstrass curves, and is cited by [`WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom`](thm.html#WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eq_of_infinite_setOf_equation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.eq_of_infinite_setOf_equation
    {F : Type*} [Field F] {W V : WeierstrassCurve F}
    (h : {xy : F × F | W.toAffine.Equation xy.1 xy.2 ∧ V.toAffine.Equation xy.1 xy.2}.Infinite) :
    W = V := by sorry
