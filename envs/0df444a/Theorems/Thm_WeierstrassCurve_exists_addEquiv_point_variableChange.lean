-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
-- name    : WeierstrassCurve.exists_addEquiv_point_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/8de1afe9-e422-5510-9234-bbf863be0ba2
-- title:
--   Variable change induces an isomorphism of point groups
-- statement:
--   Let $K$ be a field, let $W$ be a Weierstrass curve over $K$ (given by coefficients $a_1,a_2,a_3,a_4,a_6$), and let $C$ be a Weierstrass variable change over $K$, that is a quadruple consisting of a unit $u \in K^\times$ and scalars $r,s,t \in K$. Write $C \bullet W$ for the Weierstrass curve obtained from $W$ by the action of $C$. The assertion is that there exists an isomorphism of additive groups $e \colon W^{\mathrm{aff}}(K) \to (C \bullet W)^{\mathrm{aff}}(K)$ between the groups of points of the associated affine Weierstrass curves (nonsingular $K$-rational affine points together with the point at infinity, with the chord–tangent addition), with the following property: for all $x,y \in K$ and every proof $h$ that $(x,y)$ is a nonsingular point of the affine curve attached to $W$, the pair $$\bigl(u^{-2}(x-r),\; u^{-3}(y - sx + (sr - t))\bigr)$$ is a nonsingular point of the affine curve attached to $C \bullet W$, and $e$ sends the affine point $(x,y)$ of $W$ to that point of $C \bullet W$. No claim beyond additivity and bijectivity is made about the behaviour of $e$ at the point at infinity.
--
--   This is the elementary statement that two Weierstrass models related by an admissible change of coordinates $(x,y) = (u^2x' + r,\, u^3y' + u^2sx' + t)$ have isomorphic groups of $K$-rational points, with the isomorphism written out in coordinates by the inverse substitution. It is used to transport explicit points and point-group computations between models of one elliptic curve, and is invoked in the Čerednik–Drinfel'd part of the development when comparing curves differing by a variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_addEquiv_point_variableChange.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_addEquiv_point_variableChange {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (C : VariableChange K) : ∃ e : W.toAffine.Point ≃+ (C • W).toAffine.Point, ∀ (x y : K) (h : W.toAffine.Nonsingular x y), ∃ h' : (C • W).toAffine.Nonsingular ((↑C.u⁻¹ : K) ^ 2 * (x - C.r)) ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))), e (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some ((↑C.u⁻¹ : K) ^ 2 * (x - C.r)) ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))) h' := by sorry
