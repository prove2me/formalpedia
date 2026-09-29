-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
-- name    : WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e530f3fb-5431-5292-ae33-fcf0cdb4287f
-- title:
--   nP=O if and only if ψₙ(P)=0
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$, given by its five coefficients and not assumed to be nonsingular as a curve. Let $x,y \in F$ satisfy `W.toAffine.Nonsingular x y`, i.e. $(x,y)$ lies on the affine Weierstrass equation of $W$ and is a nonsingular point of it, so that it determines an element `WeierstrassCurve.Affine.Point.some x y h` of the group `W.toAffine.Point` of affine points of $W$, whose zero element is the point at infinity. Let $n$ be an arbitrary integer. The assertion is that the $n$-fold multiple $n \cdot (x,y)$ of this point, formed in the group of points, equals the point at infinity if and only if the $n$-th division polynomial $\psi_n$ of $W$, a bivariate polynomial over $F$ in the variables conventionally written $X$ and $Y$, vanishes when $X$ is evaluated at $x$ and $Y$ at $y$. No restriction is placed on the characteristic of $F$, on $n$ (negative and zero values included), or on the discriminant of $W$.
--
--   This is the standard characterisation of the $n$-torsion of a Weierstrass curve as the zero locus of the $n$-th division polynomial, in the form convenient for computing with explicit points. It is the basic bridge between the group law and division-polynomial algebra used throughout the study of Frobenius endomorphisms and of torsion subschemes, for instance in the computations of degrees of kernels of Frobenius-type endomorphisms and in comparisons of Galois actions on torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by sorry
