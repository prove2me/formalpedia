-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq
-- name    : WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/0e2e93f4-dcdc-511a-bbcd-8d240e2033d0
-- title:
--   A variable change is determined by its map on points
-- statement:
--   Let $F$ be an algebraically closed field, let $W_1,W_2$ be Weierstrass curves over $F$ in affine form, and assume $W_1$ is elliptic in the sense of Mathlib's `IsElliptic` (invertible discriminant). Let $C,C'$ be Weierstrass variable changes over $F$, i.e. quadruples $(u,r,s,t)$ with $u$ a unit of $F$, and suppose both transform $W_2$ into $W_1$: $C \bullet W_2 = W_1$ and $C' \bullet W_2 = W_1$. Each such equality yields, via `Point.equivOfVariableChangeEq`, a bijection $W_1(F) \to W_2(F)$ of the groups of affine points together with the point at infinity, obtained by transporting the bijection `variableChangeEquiv` along the equality of curves; concretely it is the map given on affine points by the usual substitution attached to $(u,r,s,t)$ and fixing the point at infinity. The hypothesis is that these two bijections agree at every point $P$ of $W_1$. The conclusion is that $C = C'$ as variable changes, that is, $u=u'$, $r=r'$, $s=s'$ and $t=t'$.
--
--   This is the uniqueness half of the classical statement that an isomorphism between curves in Weierstrass form is induced by a unique change of coordinates $(u,r,s,t)$ (Silverman, AEC III.3.1(b)). It is used in the comparison of the group of variable changes fixing a curve with its group of rational automorphisms, and in the place-theoretic dictionary for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
    {C C' : WeierstrassCurve.VariableChange F} (hC : C • W₂ = W₁) (hC' : C' • W₂ = W₁)
    (h : ∀ P : W₁.Point, Point.equivOfVariableChangeEq hC P = Point.equivOfVariableChangeEq hC' P) :
    C = C' := by sorry
