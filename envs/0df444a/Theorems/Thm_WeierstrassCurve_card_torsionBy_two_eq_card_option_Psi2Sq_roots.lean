-- Prove2me | Theorems.Thm_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots
-- name    : WeierstrassCurve.card_torsionBy_two_eq_card_option_Psi2Sq_roots
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/2428e253-6f07-59bd-af6c-2dfff1423321
-- title:
--   #E[2] = 1 + #{Ψ₂² = 0} in characteristic ≠ 2
-- statement:
--   Let $K$ be a field with decidable equality, and let $W$ be a Weierstrass curve over $K$ which is elliptic (its discriminant is a unit, via the `IsElliptic` instance assumption). Assume $2 \neq 0$ in $K$. Then the natural-number cardinality of the $2$-torsion of the group of points of the associated affine curve — that is, of the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ W.toAffine.Point 2` of elements $P$ with $2 \cdot P = 0$, the group law being Mathlib's addition on `WeierstrassCurve.Affine.Point`, which includes the point at infinity — equals the cardinality of `Option {x : K // W.Ψ₂Sq.eval x = 0}`, i.e. one more than the number of roots in $K$ of the polynomial $\Psi_2^2 = 4X^3 + b_2X^2 + 2b_4X + b_6$. The assertion is an equality of `Nat.card`s of the two types, so it is the numerical count of $K$-rational $2$-torsion points; no explicit bijection is part of the statement, and no finiteness hypothesis is imposed on $K$.
--
--   This is the classical description of the $2$-torsion of an elliptic curve in characteristic $\neq 2$: besides the point at infinity, the $2$-torsion points are exactly the points $(x, -(a_1x+a_3)/2)$ with $x$ a root of the $2$-division polynomial. It is used to count the $2$-torsion of reductions of the Frey curve, in [`FreyCurve.card_two_torsion_reductionMod`](thm.html#FreyCurve.card_two_torsion_reductionMod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

theorem card_torsionBy_two_eq_card_option_Psi2Sq_roots {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point 2) =
      Nat.card (Option {x : K // W.Ψ₂Sq.eval x = 0}) := by sorry
