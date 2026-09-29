-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point
-- name    : WeierstrassCurve.VariableChange.nonempty_addEquiv_affine_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/13e5d2e6-0104-5dce-a83c-8c7b6adb3497
-- title:
--   A variable change induces an isomorphism of affine point groups
-- statement:
--   Let $L$ be a field and let $W$ be a Weierstrass curve over $L$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, and let $C$ be an element of `WeierstrassCurve.VariableChange L`, that is an admissible change of Weierstrass variables $(u,r,s,t)$ with $u$ a unit of $L$. Write $C \bullet W$ for the curve obtained by acting with $C$ on $W$. The assertion is that the type of additive equivalences from the group of points of the affine curve underlying $C \bullet W$ to the group of points of the affine curve underlying $W$ is nonempty; here, for a Weierstrass curve over a field, `WeierstrassCurve.Affine.Point` denotes the set consisting of a point at infinity together with the nonsingular $L$-rational affine solutions of the Weierstrass equation, equipped with the chord–tangent addition. Thus the two point groups are isomorphic as additive groups. Note that the statement produces only the nonemptiness of the type of isomorphisms, not a named isomorphism, and that no nonsingularity or nonvanishing-discriminant hypothesis on $W$ is imposed.
--
--   This is the standard fact that an admissible change of Weierstrass variables is an isomorphism of the associated groups of nonsingular rational points, so that the group structure is an invariant of the curve up to such changes. It is used in the analysis of curves that are not elliptic, for instance in [`WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero`](thm.html#WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero), where one first moves a singular Weierstrass equation into a normal form by a variable change and then computes with the resulting point group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.VariableChange.nonempty_addEquiv_affine_point
    {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve L)
    (C : WeierstrassCurve.VariableChange L) :
    Nonempty ((C • W).toAffine.Point ≃+ W.toAffine.Point) := by sorry
