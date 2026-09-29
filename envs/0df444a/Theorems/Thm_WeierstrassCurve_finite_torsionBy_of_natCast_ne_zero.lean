-- Prove2me | Theorems.Thm_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero
-- name    : WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/8a534e52-d39c-55e9-af16-ca242f72b778
-- title:
--   Finiteness of n-torsion when n ≠ 0 in k
-- statement:
--   Let $k$ be a field and let $W$ be a Weierstrass curve over $k$ which is elliptic (in the sense of Mathlib's `IsElliptic`: its discriminant is a unit). Let $n$ be a natural number whose image in $k$ is nonzero. Then the $\mathbb{Z}$-submodule $\mathrm{torsionBy}\ \mathbb{Z}\ W.\mathrm{toAffine.Point}\ n$ — that is, the subgroup of those points $P$ of the group $W(k)$ of $k$-rational points of the associated affine Weierstrass curve (the points of the affine model together with the point at infinity, with the usual chord–tangent group law) satisfying $n \cdot P = 0$ — is a finite type. Note that the hypothesis $(n : k) \neq 0$ already forces $n \neq 0$, so there is no separate nondegeneracy assumption; nothing is asserted about the structure of this group, only its finiteness.
--
--   This is the standard finiteness of the $n$-torsion of the group of rational points of an elliptic curve over a field of residue characteristic not dividing $n$, obtained from the fact that over an algebraically closed field the $n$-torsion has exactly $n^2$ elements. It serves as the finiteness guarantee underlying the torsion-subgroup counts used in the modular-curve part of the development, and is cited by [`ModularCurve.finite_cycSub`](thm.html#ModularCurve.finite_cycSub) and by [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero (k : Type*) [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := by sorry
