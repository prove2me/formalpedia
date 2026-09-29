-- Prove2me | Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le
-- name    : ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/b3c9a44e-7d1e-513c-8186-3ed6ccbedaac
-- title:
--   Vanishing of Hⁱ(Pⁿ_R,𝒪(d)) for i≥ 1, d≥ -n
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and let $d$ be an integer satisfying $-(n:\mathbb{Z}) \le d$. Let $i$ be a natural number with $1 \le i$. The assertion is that the $R$-module $\mathtt{ProjSpaceCech.Twist.H } R\ n\ d\ i$ is a subsingleton, i.e. has at most one element. By definition this object is, in degree $0$, the kernel of the map [`ProjSpaceCech.Twist.d R n d 0`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107), and in a positive degree $i = j+1$ the quotient of the kernel of [`ProjSpaceCech.Twist.d R n d (j+1)`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107) by the submodule obtained by pulling back the range of [`ProjSpaceCech.Twist.d R n d j`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107) along the inclusion of that kernel; thus, in the range of indices covered by the hypothesis $1 \le i$, it is the $i$-th cohomology $\ker d^{\,i}/\operatorname{im} d^{\,i-1}$ of the complex formed by the maps [`ProjSpaceCech.Twist.d`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107), and being a subsingleton means exactly that this cohomology vanishes. No hypothesis is placed on $R$ beyond commutativity, and $n = 0$ is allowed (then $d \ge 0$).
--
--   This is Serre's vanishing theorem for the twisting sheaves on projective space in the form $H^i(\mathbb{P}^n_R,\mathcal{O}(d)) = 0$ for all $i \ge 1$ and all $d \ge -n$, computed through the alternating Čech complex for the standard cover by the loci $D_+(x_j)$. The degrees $0 < i < n$ and $i > n$ come from [`ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le`](thm.html#ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le) and [`ProjSpaceCech.Twist.subsingleton_cohomology_of_lt`](thm.html#ProjSpaceCech.Twist.subsingleton_cohomology_of_lt), so the content lies in the top degree $i = n$; the statement serves as the base case, for finite direct sums of shifted free modules, of the vanishing result [`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`](thm.html#ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG) for finitely generated graded modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le (R : Type u) [CommRing R] (n : ℕ) {d : ℤ} (hd : -(n : ℤ) ≤ d) {i : ℕ} (hi : 1 ≤ i) :
    Subsingleton (ProjSpaceCech.Twist.H R n d i) := by sorry
