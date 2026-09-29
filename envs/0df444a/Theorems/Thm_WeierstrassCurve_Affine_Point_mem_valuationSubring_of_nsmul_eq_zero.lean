-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_mem_valuationSubring_of_nsmul_eq_zero
-- name    : WeierstrassCurve.Affine.Point.mem_valuationSubring_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/a45815f0-61ba-52cb-aa45-fed204041bfc
-- title:
--   Integrality of x for odd torsion prime to the residue characteristic
-- statement:
--   Let $K$ be a field and $A \subseteq K$ a valuation subring, and let $W$ be a Weierstrass curve over $K$ which is elliptic (its discriminant is invertible) and whose coefficients $a_1, a_2, a_3, a_4, a_6$ all lie in $A$. Let $n$ be a natural number which is odd and whose image $(n : K)$ does not lie in `A.nonunits`, i.e. the valuation of $n$ is not $< 1$; since $n$ is in any case an element of $A$, this says exactly that $n$ is a unit of $A$. Let $x, y \in K$ be such that $(x,y)$ is a nonsingular point of the affine curve attached to $W$, so that it defines an element `Point.some x y h` of the group of affine points of `W.toAffine`. If $n \cdot (x,y) = 0$ in that group, then $x \in A$. No hypothesis is imposed on the reduction behaviour of $W$ beyond integrality of the coefficients; in particular the discriminant need not be a unit of $A$, and $A$ is not assumed complete or discrete.
--
--   This is the $x$-coordinate form of the statement that the kernel of reduction contains no nonzero torsion of odd order prime to the residue characteristic: such torsion points have integral abscissa. It is used at the prime $2$ for the Frey curve, in [`FreyPackage.frey_wild_inertia_at_two_trivial`](thm.html#FreyPackage.frey_wild_inertia_at_two_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_mem_valuationSubring_of_nsmul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.mem_valuationSubring_of_nsmul_eq_zero {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K) (W : WeierstrassCurve K) [W.IsElliptic] (h₁ : W.a₁ ∈ A) (h₂ : W.a₂ ∈ A) (h₃ : W.a₃ ∈ A) (h₄ : W.a₄ ∈ A) (h₆ : W.a₆ ∈ A) {n : ℕ} (hn : Odd n) (hnA : (n : K) ∉ A.nonunits) {x y : K} (h : W.toAffine.Nonsingular x y) (hP : n • Point.some x y h = 0) : x ∈ A := by sorry
