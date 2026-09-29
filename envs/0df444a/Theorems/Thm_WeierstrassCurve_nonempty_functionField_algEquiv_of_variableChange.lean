-- Prove2me | Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
-- name    : WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/3a47c5d0-7fb4-5cce-bd99-11dd0f3e9e6b
-- title:
--   Variable changes induce isomorphic Weierstrass function fields
-- statement:
--   Let $F$ be a field, let $W$ be a Weierstrass curve over $F$ (given by the coefficients $a_1,a_2,a_3,a_4,a_6$), and let $C$ be an admissible change of variables over $F$, i.e. a quadruple $(u,r,s,t)$ with $u \in F^\times$ and $r,s,t \in F$, acting on Weierstrass curves by the substitution $(x,y) \mapsto (u^2x+r,\ u^3y+su^2x+t)$; write $C \bullet W$ for the transformed curve. The assertion is that the type of $F$-algebra isomorphisms between the function field of the affine curve underlying $W$ and the function field of the affine curve underlying $C \bullet W$ is nonempty; here the function field of an affine Weierstrass curve is the fraction field of its coordinate ring, viewed as an $F$-algebra. Thus the two function fields are isomorphic over $F$. The conclusion is stated as nonemptiness, so no particular isomorphism is named; in particular the statement does not record that the isomorphism is the one given by the substitution above, nor that it is compatible with the inclusions of $F(x)$ as a rational function field.
--
--   This is the standard fact that an admissible change of Weierstrass coordinates is a birational (indeed biregular) change of model, so it leaves the function field unchanged up to $F$-isomorphism. It provides the easy direction of the correspondence between $F$-isomorphisms of Weierstrass function fields and variable changes, and is used in the results deducing equality of $j$-invariants, and comparisons of kernels of maps on points, from an isomorphism of function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
    {F : Type u} [Field F] (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField) := by sorry
