-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six
-- name    : WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/233bf493-30e9-5d89-8b71-c9e138076112
-- title:
--   Variable change fixing a Weierstrass curve with u=1 is trivial
-- statement:
--   Let $R$ be a commutative ring in which $6$ is a unit, let $W$ be a Weierstrass curve over $R$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, and let $C$ be a Weierstrass variable change over $R$, that is a quadruple consisting of a unit $u$ of $R$ and elements $r,s,t$ of $R$, acting on Weierstrass curves by the usual substitution formulas $(x,y)\mapsto(u^2x+r,\;u^3y+u^2sx+t)$. Assume that $C$ fixes $W$, i.e. $C \bullet W = W$ as Weierstrass curves (equality of all five coefficients), and that $C.u = 1$. Then $C$ equals the identity variable change, i.e. $C = 1$, which unfolds to $u = 1$ and $r = s = t = 0$. Thus the conclusion is that the unipotent part of the stabiliser of a Weierstrass curve is trivial as soon as $2$ and $3$ are invertible; no smoothness or nonsingularity hypothesis on $W$ is imposed.
--
--   This is the standard rigidity statement for the change-of-variables action on Weierstrass equations: away from residue characteristics $2$ and $3$, an automorphism of a Weierstrass curve is determined by its scalar $u$. It is used in the analysis of relabelling actions on level moduli data, where it forces the residue scalar of a nontrivial automorphism to differ from $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six
    (R : Type) [CommRing R] (h6 : IsUnit (6 : R))
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (hC : C • W = W) (hu : C.u = 1) :
    C = 1 := by sorry
