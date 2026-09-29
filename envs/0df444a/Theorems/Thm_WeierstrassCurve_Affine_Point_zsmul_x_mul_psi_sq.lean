-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
-- name    : WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4e980a47-c6f1-516e-9c4a-8bd6da366a06
-- title:
--   x([n]P) ψₙ(P)²=φₙ(P) for affine points
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ whose discriminant is a unit, and let $n\in\mathbb{Z}$. Suppose $x,y\in F$ are such that $(x,y)$ is a nonsingular point of the affine curve `W.toAffine`, with associated group element `WeierstrassCurve.Affine.Point.some x y h`, and likewise $x',y'\in F$ with `W.toAffine.Nonsingular x' y'`. Assume that the $n$-fold multiple of $(x,y)$ in the group of affine points equals $(x',y')$, that is $n \bullet$ `some x y h` $=$ `some x' y' h'` (in particular $[n]$ applied to the point is not the point at infinity, since it is given in affine form). Then $$x' \cdot \big(\psi_n(x,y)\big)^2 = \varphi_n(x,y),$$ where $\psi_n =$ `W.ψ n` and $\varphi_n =$ `W.φ n` are the bivariate division polynomials in $F[X][Y]$ attached to $W$ and evaluation is `Polynomial.evalEval x y`. Equivalently $x([n]P)=\varphi_n(P)/\psi_n(P)^2$, stated in cleared-denominator form; negative $n$ are included.
--
--   This is the multiplication-by-$n$ formula for the $x$-coordinate in terms of division polynomials, in the form with denominators cleared. It is used throughout the study of the Frobenius endomorphism over finite fields, where degrees of the rational functions $\varphi_n/\psi_n^2$ control kernels of $[m]-\pi$ and torsion counts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq.lean

import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ) {x y : F} (h : W.toAffine.Nonsingular x y) {x' y' : F} (h' : W.toAffine.Nonsingular x' y') (hn : n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h') : x' * ((W.ψ n).evalEval x y) ^ 2 = (W.φ n).evalEval x y := by sorry
