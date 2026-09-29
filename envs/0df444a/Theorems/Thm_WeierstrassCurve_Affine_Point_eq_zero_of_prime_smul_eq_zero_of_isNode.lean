-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode
-- name    : WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d428a7f0-1499-5676-be6e-54b7186b07d3
-- title:
--   No p-torsion on the nonsingular locus of a nodal cubic
-- statement:
--   Let $k$ be a field of characteristic $p$, where $p$ is a prime, and let $W$ be a Weierstrass curve over $k$, given by coefficients $a_1,\dots,a_6$. Suppose $x_0,y_0 \in k$ satisfy the affine Weierstrass equation of $W$ (`W.toAffine.Equation x₀ y₀`) but are not a nonsingular point of it (`¬ W.toAffine.Nonsingular x₀ y₀`), so that $(x_0,y_0)$ is a singular point of the cubic; suppose further that $b_2 + 12x_0 \neq 0$, where $b_2 = a_1^2 + 4a_2$ is the usual Weierstrass invariant — the condition saying that the singularity at $(x_0,y_0)$ is a node rather than a cusp, i.e. that the tangent cone there splits into two distinct lines over an algebraic closure. Then the group $W.toAffine.Point$ of nonsingular points of $W$ — the point at infinity together with the affine solutions at which the curve is nonsingular, under the chord–tangent law — has no nonzero $p$-torsion: any $P$ with $p \cdot P = 0$ equals $0$.
--
--   This is the statement that the nonsingular locus of a nodal Weierstrass cubic in characteristic $p$, being a one-dimensional torus (a form of $\mathbb{G}_m$), contains no nontrivial $p$-torsion; the corresponding assertion fails for a cuspidal cubic, whose nonsingular locus is $\mathbb{G}_a$. It is used in the analysis of an elliptic curve with multiplicative reduction at $p$, to show that $p$-torsion points lying in the identity component of the reduction are in the kernel of reduction, and is cited by [`WeierstrassCurve.inZeroComponentAt_torsionBy_residueChar`](thm.html#WeierstrassCurve.inZeroComponentAt_torsionBy_residueChar) and [`WeierstrassCurve.psiSq_ne_zero_of_nodal`](thm.html#WeierstrassCurve.psiSq_ne_zero_of_nodal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode {k : Type*} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0) (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by sorry
