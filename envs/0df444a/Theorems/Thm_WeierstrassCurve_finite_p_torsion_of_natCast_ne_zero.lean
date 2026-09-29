-- Prove2me | Theorems.Thm_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero
-- name    : WeierstrassCurve.finite_p_torsion_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/05a466c5-256d-5b0e-afb3-f429c145d4ff
-- title:
--   Finiteness of E[p] when p ≠ 0 in F
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ which is elliptic, i.e. carries the `IsElliptic` instance (invertible discriminant). Let $p$ be a natural number which is prime, satisfies $5 \le p$, and whose image in $F$ is nonzero, so that the characteristic of $F$ does not divide $p$. The conclusion is that the $p$-torsion of the group of $F$-points of the associated affine Weierstrass curve, namely the $\mathbb{Z}$-submodule $\mathrm{Submodule.torsionBy}\ \mathbb{Z}\ W.\mathrm{toAffine}.\mathrm{Point}\ p$ consisting of those points $P$ with $p \cdot P = 0$, is a finite type. Note that the assertion is bare finiteness of $E[p](F)$, with no bound on its cardinality and no claim about its group structure; the points are the $F$-rational points only, and no separate hypothesis on the characteristic of $F$ beyond $(p : F) \neq 0$ is imposed.
--
--   This is the standard finiteness of the $p$-torsion of an elliptic curve in characteristic not dividing $p$, obtained from the fact that the abscissa of a nonzero $p$-torsion point is a root of the $p$-th division polynomial, which is nonzero because $p$ is invertible in $F$, together with the fact that each abscissa supports at most two points. It is used in the analysis of the Tate curve, in [`TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero`](thm.html#TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.finite_p_torsion_of_natCast_ne_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) : Finite (Submodule.torsionBy ℤ W.toAffine.Point p) := by sorry
