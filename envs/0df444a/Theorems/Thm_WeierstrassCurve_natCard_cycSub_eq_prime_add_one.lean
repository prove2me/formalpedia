-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_cycSub_eq_prime_add_one
-- name    : WeierstrassCurve.natCard_cycSub_eq_prime_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/a8710e65-64dc-5ba9-a86a-a524258e86f3
-- title:
--   An elliptic curve has p+1 cyclic subgroups of order p
-- statement:
--   Let $F$ be an algebraically closed field and let $W$ be a Weierstrass curve over $F$ which is elliptic (so that its affine points $W.\mathrm{toAffine}.\mathrm{Point}$ carry the usual group law). Let $p$ be a prime number, and assume that the images of $p$ and of $2$ in $F$ are both nonzero. Then the type of subgroups $G$ of the additive group of points of $W$ for which there exists a point $g$ of additive order exactly $p$ with $G$ equal to the subgroup $\mathrm{AddSubgroup.zmultiples}\,g$ of integer multiples of $g$ has cardinality (in the sense of `Nat.card`) equal to $p+1$. In other words, the cyclic subgroups of order $p$ of the group of $F$-points of $W$ number exactly $p+1$. No finiteness of the point group is assumed; finiteness of the relevant sets is derived from the $p$-torsion count.
--
--   This is the standard count of the order-$p$ subgroups of $E[p]\cong(\mathbb{Z}/p)^2$ for an elliptic curve over an algebraically closed field of residue characteristic different from $p$, i.e. the count of the $p+1$ cyclic subgroups parametrised classically by the cusps/degeneracies of level-$p$ structures. It is used in the project to produce a point of exact order $p$ on such a curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_cycSub_eq_prime_add_one.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_cycSub_eq_prime_add_one {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp : (p : F) ≠ 0) (h2 : (2 : F) ≠ 0) :
    Nat.card {G : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = p ∧ G = AddSubgroup.zmultiples g} = p + 1 := by sorry
