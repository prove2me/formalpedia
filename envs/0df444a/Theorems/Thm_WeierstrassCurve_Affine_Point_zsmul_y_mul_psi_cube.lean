-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube
-- name    : WeierstrassCurve.Affine.Point.zsmul_y_mul_psi_cube
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4fdd4635-b19d-59ac-890e-7c8f296bee29
-- title:
--   y([n]P) ψₙ(P)³=ωₙ(P) for affine points
-- statement:
--   Let $F$ be a field and $W$ a Weierstrass curve over $F$ whose associated elliptic-curve condition `W.IsElliptic` holds (discriminant a unit), let $n$ be an integer, and let $(x,y)$ and $(x',y')$ be pairs of elements of $F$ together with proofs $h$, $h'$ that each is a nonsingular point of the affine curve `W.toAffine`, so that `Point.some x y h` and `Point.some x' y' h'` are elements of the group $W(F)$ of affine points. Assume $n \cdot (x,y) = (x',y')$ in that group, computed with the Mathlib group law on `WeierstrassCurve.Affine.Point`; note that this hypothesis in particular encodes that $[n]P$ is not the point at infinity. The conclusion is the single identity
--   $$y' \cdot \bigl(\psi_n(x,y)\bigr)^3 = \omega_n(x,y),$$
--   where $\psi_n$ is the Mathlib division polynomial `WeierstrassCurve.ψ` of $W$, $\omega_n$ is the project's division polynomial [`WeierstrassCurve.ω`](def/EllipticCurve_DivisionPolynomialOmega.html#L86) (the halved polynomial of the module `EllipticCurve_DivisionPolynomialOmega`, available in every characteristic), and `evalEval x y` denotes evaluation of a bivariate polynomial in $F[X][Y]$ at $X = x$, $Y = y$. No nonvanishing of $\psi_n(x,y)$ and no companion identity for the $x$-coordinate are part of the conclusion, although both are established en route.
--
--   This is the $y$-coordinate half of the classical multiplication-by-$n$ formula $[n]P = \bigl(\phi_n(P)/\psi_n(P)^2,\ \omega_n(P)/\psi_n(P)^3\bigr)$, stated here with the characteristic-free $\omega_n$ so that characteristic $2$ is included. It is used in the treatment of Frobenius and isogeny endomorphisms, for instance by [`FrobeniusEndo.exists_x_linePencil_frobEnd_mul_collision_sq`](thm.html#FrobeniusEndo.exists_x_linePencil_frobEnd_mul_collision_sq) and by the results on Weil numbers and on restricting isogeny data along places of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube.lean

import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.Point.zsmul_y_mul_psi_cube {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ) {x y : F} (h : W.toAffine.Nonsingular x y) {x' y' : F} (h' : W.toAffine.Nonsingular x' y') (hn : n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h') : y' * ((W.ψ n).evalEval x y) ^ 3 = (W.ω n).evalEval x y := by sorry
