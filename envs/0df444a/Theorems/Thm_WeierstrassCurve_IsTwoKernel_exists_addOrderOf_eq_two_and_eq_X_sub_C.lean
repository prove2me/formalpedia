-- Prove2me | Theorems.Thm_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C
-- name    : WeierstrassCurve.IsTwoKernel.exists_addOrderOf_eq_two_and_eq_X_sub_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/107c8c8f-d51c-5e0c-9a32-52349504a1a5
-- title:
--   Two-kernel polynomials are X-x(Q) with Q of order 2
-- statement:
--   Let $\Omega$ be an algebraically closed field and let $W$ be a Weierstrass curve over $\Omega$ that is elliptic, i.e. whose discriminant is a unit. Assume $2\neq 0$ in $\Omega$, and let $h\in\Omega[X]$ satisfy the predicate `IsTwoKernel` for $W$, which by definition asserts three things: the natural degree of $h$ is at most $1$, the coefficient of $X$ in $h$ equals $1$, and $h$ divides the polynomial $\Psi_2^2 = 4X^3 + b_2X^2 + 2b_4X + b_6$ attached to $W$. The conclusion is that there exists a point $Q$ of the affine curve $W$ (a point of the Weierstrass group law, either the point at infinity or an affine nonsingular solution) such that the additive order of $Q$ is exactly $2$ and $h = X - C(x)$, where $x$ is the first component of `coordsOrZero Q`, that is the $x$-coordinate of $Q$ when $Q$ is affine and $0$ when $Q$ is the point at infinity. Since a point of order $2$ is not the point at infinity, the produced $Q$ is affine and $h = X - x(Q)$.
--
--   This is the statement that the monic degree-one divisors of the $2$-division polynomial $\Psi_2^2$ are exactly the polynomials $X - x(Q)$ for $Q$ a point of order $2$, i.e. that a $2$-kernel polynomial cuts out an order-$2$ subgroup. It is used in the classification of cyclic subgroups of prime-power order on an elliptic curve over an algebraically closed field, in the $2$-primary case of the $\Gamma_0$-level-structure bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.IsTwoKernel.exists_addOrderOf_eq_two_and_eq_X_sub_C
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) [W.IsElliptic]
    (h2 : (2 : Ω) ≠ 0) (h : Polynomial Ω) (hh : W.IsTwoKernel h) :
    ∃ Q : W.toAffine.Point, addOrderOf Q = 2 ∧ h = X - C (Q.coordsOrZero).1 := by sorry
