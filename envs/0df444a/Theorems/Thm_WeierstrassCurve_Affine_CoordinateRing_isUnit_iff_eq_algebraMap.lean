-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap
-- name    : WeierstrassCurve.Affine.CoordinateRing.isUnit_iff_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/b72cf4c6-e7f7-59c3-a9e7-1f41d6a63568
-- title:
--   Units of the affine coordinate ring are the nonzero constants
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$, with affine coordinate ring $W.toAffine.CoordinateRing$, that is $F[X,Y]$ modulo the Weierstrass polynomial of $W$. For an arbitrary element $f$ of this coordinate ring, the assertion is an equivalence: $f$ is a unit in the coordinate ring if and only if there exists $c \in F$ with $c \neq 0$ such that $f$ is the image of $c$ under the structure map $F \to W.toAffine.CoordinateRing$. Thus the unit group of the affine coordinate ring is exactly the image of $F^{\times}$ under the algebra map, the scalars; no irreducibility, nonsingularity or discriminant hypothesis on $W$ is required, and no hypothesis beyond $F$ being a field is imposed.
--
--   This is the coordinate-ring form of the classical principle that a regular function without zeros on the affine part $E \setminus \{O\}$ of a Weierstrass cubic is constant, i.e. $\mathcal{O}(E \setminus \{O\})^{\times} = F^{\times}$. It is used in the comparison of Weil pairings under a change of variables, in [`WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange`](thm.html#WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.CoordinateRing.isUnit_iff_eq_algebraMap {F : Type*} [Field F] {W : WeierstrassCurve F} (f : W.toAffine.CoordinateRing) : IsUnit f ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.CoordinateRing c := by sorry
