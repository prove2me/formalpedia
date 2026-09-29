-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero
-- name    : WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/7fd69e46-843e-56fe-85fd-0119bf960879
-- title:
--   Torsion point coordinates are integral over the base field
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra, let $W$ be a Weierstrass curve over $F$ which is elliptic (so its discriminant is a unit), and let $n$ be an integer whose image in $F$ is nonzero. Let $x, y \in L$ be such that $(x,y)$ is a nonsingular point of the affine Weierstrass curve $W\!\!\mathbin{⁄}L$ obtained from $W$ by base change along $\mathrm{algebraMap}\,F\,L$, i.e. $(x,y)$ satisfies the affine Weierstrass equation of $W\!\!\mathbin{⁄}L$ and the two partial derivatives do not vanish simultaneously there. Assume that the corresponding point $\mathrm{some}\,x\,y$ of the group $(W\!\!\mathbin{⁄}L)(L)$ of affine points is killed by $n$, that is $n \cdot \mathrm{some}\,x\,y = 0$ for the integer scalar action on the additive group of points. The conclusion is that both coordinates are integral over $F$: $x$ is integral over $F$ and $y$ is integral over $F$. Since $F$ is a field, this is the same as saying that $x$ and $y$ are algebraic over $F$.
--
--   This is the standard fact that the coordinates of an $n$-torsion point of an elliptic curve, for $n$ invertible in the base field, are algebraic over that base field, so that all such torsion is defined over the algebraic closure. It is used in the study of torsion of Tate curves and of elliptic curves over $p$-adic fields, notably by [`TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two`](thm.html#TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_eq_two), [`TateCurve.torsionBy_baseChange_bijective_algebraicClosure_padic`](thm.html#TateCurve.torsionBy_baseChange_bijective_algebraicClosure_padic) and [`WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic`](thm.html#WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_isElliptic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in

theorem WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero
    {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {W : WeierstrassCurve F} [W.IsElliptic] {n : ℤ} (hn : (n : F) ≠ 0)
    {x y : L} (hns : (W⁄L).Nonsingular x y)
    (hQ : n • (WeierstrassCurve.Affine.Point.some x y hns : (W⁄L).Point) = 0) :
    _root_.IsIntegral F x ∧ _root_.IsIntegral F y := by sorry
