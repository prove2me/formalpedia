-- Prove2me | Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le
-- name    : ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/071d11a9-6ed3-55f6-bf11-33900d4aca82
-- title:
--   Vanishing of Hⁱ(Pⁿ_R,𝒪(d)) for 0<i<n
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, let $d$ be an integer, and let $i$ be a natural number satisfying $i+2\le n$. Consider the project's Čech-type complex of $R$-modules attached to the $d$-th twist on projective $n$-space, with differentials [`ProjSpaceCech.Twist.d R n d`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107), and its cohomology types [`ProjSpaceCech.Twist.H R n d`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L142), defined in degree $0$ as the kernel of the differential out of degree $0$ and, in degree $j+1$, as the quotient of $\ker(d^{\,j+1})$ by the preimage, under the inclusion of $\ker(d^{\,j+1})$ into the degree-$(j+1)$ term, of the range of $d^{\,j}$, i.e. by $\operatorname{im}(d^{\,j})\cap\ker(d^{\,j+1})$. The assertion is that the type $H^{i+1}$, namely $\ker(d^{\,i+1})/(\operatorname{im}(d^{\,i})\cap\ker(d^{\,i+1}))$, is a subsingleton: any two of its elements are equal. Since it is a quotient of a module, this is the vanishing $H^{i+1}=0$; as $i$ ranges over the natural numbers with $i+2\le n$, it gives the vanishing of the cohomology of the twisted sheaf in all degrees strictly between $0$ and $n$, for every commutative ring $R$ and every twist $d$, with no Noetherian or field hypothesis.
--
--   This is Serre's computation of the cohomology of the line bundles $\mathcal{O}(d)$ on $\mathbb{P}^n_R$ in the intermediate degrees, realised on the alternating Čech complex of the standard affine cover by Laurent-monomial modules. It feeds into [`ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le`](thm.html#ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le), which packages the vanishing statements for the twisted sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : i + 2 ≤ n) : Subsingleton (ProjSpaceCech.Twist.H R n d (i + 1)) := by sorry
