-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
-- name    : WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4a97bf48-6b69-52ce-8cff-90d549d4705d
-- title:
--   2P=O iff x is a root of Ψ₂²
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$, given by coefficients $a_1,a_2,a_3,a_4,a_6$. Let $x,y \in F$ and suppose $h$ witnesses that $(x,y)$ is a nonsingular point of the affine Weierstrass model $W$, i.e. that the Weierstrass equation holds at $(x,y)$ and that the two partial derivatives of the equation do not both vanish there. Writing $P$ for the corresponding point `WeierstrassCurve.Affine.Point.some x y h` in the group of points of the affine model, with identity the point at infinity $0$, the assertion is the equivalence
--   $$2 \cdot P = 0 \iff \Psi_2^2(x) = 0,$$
--   where $\Psi_2^2$ is the Mathlib polynomial `WeierstrassCurve.Ψ₂Sq` attached to $W$, namely $4X^3 + b_2X^2 + 2b_4X + b_6$ in terms of the usual quantities $b_2 = a_1^2 + 4a_2$, $b_4 = 2a_4 + a_1a_3$, $b_6 = a_3^2 + 4a_6$, and $\Psi_2^2(x)$ denotes its evaluation at $x$. No restriction on the characteristic of $F$ is imposed, and $W$ is not assumed to be elliptic (no invertibility of the discriminant is required).
--
--   This is the standard characterisation of the nontrivial $2$-torsion points of a Weierstrass curve as the affine points whose $x$-coordinate is a root of the $2$-division polynomial. It is used throughout the torsion-theoretic parts of the development, for instance in the analysis of $2$-torsion on moduli points and in computations with torsion point rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by sorry
