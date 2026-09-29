-- Prove2me | Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt
-- name    : ProjSpaceCech.Twist.subsingleton_cohomology_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/cb72626c-d8cf-586f-8b53-a3ec311f4758
-- title:
--   Vanishing of Hⁱ for i>n in the twist complex
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, let $d$ be an integer, and let $i$ be a natural number with $n < i$. The assertion is that the type [`ProjSpaceCech.Twist.H R n d i`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L142) is a subsingleton, i.e. any two of its elements are equal. Here [`ProjSpaceCech.Twist.H R n d`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L142) is defined degreewise from the differentials [`ProjSpaceCech.Twist.d R n d`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107) of the project's Čech-type cochain complex attached to $\mathbb{P}^n_R$ and the twist by $d$: in degree $0$ it is the kernel of [`ProjSpaceCech.Twist.d R n d 0`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107), and in degree $j+1$ it is the quotient of the kernel of [`ProjSpaceCech.Twist.d R n d (j+1)`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107) by the preimage, under the inclusion of that kernel into the module of $(j+1)$-cochains, of the range of [`ProjSpaceCech.Twist.d R n d j`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107). Thus for $i$ exceeding $n$ the $i$-th cohomology module of the complex is zero, stated in the form that its underlying type has at most one element.
--
--   This is the vanishing of the cohomology of $\mathcal{O}(d)$ on $\mathbb{P}^n_R$ above the dimension, in the explicit alternating Čech model for the standard cover by the loci $D_+(x_j)$, $0 \le j \le n$. It is used in the companion statement [`ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le`](thm.html#ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le) and, through it, in the finiteness statements for the cohomology of the twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.subsingleton_cohomology_of_lt (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) := by sorry
