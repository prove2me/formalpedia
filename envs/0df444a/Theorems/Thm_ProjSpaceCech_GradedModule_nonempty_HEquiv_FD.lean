-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
-- name    : ProjSpaceCech.GradedModule.nonempty_HEquiv_FD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/250a164f-5ade-50fd-b978-ed6a9a551c9c
-- title:
--   Two models of Hⁱ(Pⁿ_R,𝒪(d₀)) agree
-- statement:
--   For a commutative ring $R$, natural numbers $n$ and $i$ and an integer $d_0$, the statement asserts that the type of $R$-linear equivalences between two $R$-modules is nonempty. The first module is [`ProjSpaceCech.Twist.H R n d₀ i`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L142), the $i$-th cohomology of the complex with differentials [`ProjSpaceCech.Twist.d R n d₀`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L107): for $i = 0$ it is the kernel of the differential in degree $0$, and for $i+1$ it is the kernel of the differential in degree $i+1$ modulo the preimage, under the inclusion of that kernel, of the range of the differential in degree $i$. The second is [`ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L399), formed in exactly the same way from the differentials [`ProjSpaceCech.GradedModule.d`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L386) of the graded module [`ProjSpaceCech.GradedModule.FD R n d₀`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L559), namely `GradedModule.shift (GradedModule.free R n) d₀`: its underlying module is $R[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n+1)) R`, its grading places in degree $d$ the homogeneous polynomials of degree $d + d_0$ (and the zero submodule when $d + d_0 < 0$), and its $n+1$ commuting operators are multiplication by the variables $x_j$. Thus the conclusion is the bare existence of an isomorphism, with no named map.
--
--   This identifies the Laurent-monomial model for the Čech cohomology of $\mathcal{O}(d_0)$ on $\mathbb{P}^n_R$ with the model obtained from the graded module $S(d_0)$, $S = R[x_0,\dots,x_n]$, so that Serre's explicit computation in the first model transports to the second. It is used by [`ProjSpaceCech.GradedModule.finite_cohomology_FD`](thm.html#ProjSpaceCech.GradedModule.finite_cohomology_FD) and [`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`](thm.html#ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.nonempty_HEquiv_FD (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Nonempty (ProjSpaceCech.Twist.H R n d₀ i ≃ₗ[R] ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) := by sorry
