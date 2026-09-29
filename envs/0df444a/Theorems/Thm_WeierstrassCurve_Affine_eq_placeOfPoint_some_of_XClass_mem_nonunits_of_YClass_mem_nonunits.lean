-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
-- name    : WeierstrassCurve.Affine.eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ea6ca28e-5425-5a6f-b3c4-b511c0ce9cf4
-- title:
--   A place centred at (x,y) is the gate's place of (x,y)
-- statement:
--   Let $F$ be a field with decidable equality and let $W$ be an affine Weierstrass curve over $F$, subject to three instance hypotheses: a `GenusOnePlaceGate` structure on $W$, that is, a bijection `pointEquivPlace` between the point set `W.Point` and the places of the function field `W.FunctionField` over $F$ (a place being a valuation subring containing the image of $F$, distinct from the whole field and a principal ideal ring) all of whose places have degree $1$, with `placeOfPoint` denoting this bijection; the centring mixin `GenusOnePlaceGate.IsCentred`, which requires that for every nonsingular affine point $(x,y)$ the images in the function field of the coordinate-ring classes `CoordinateRing.XClass W x` and `CoordinateRing.YClass W (Polynomial.C y)` lie in the nonunits of the valuation subring of `placeOfPoint (Point.some x y h)`; and that `W.CoordinateRing` is a Dedekind domain. Let $x,y\in F$ with `h : W.Nonsingular x y`, and let $v$ be a place of `W.FunctionField` over $F$ whose valuation subring contains both of those images among its nonunits. Then $v$ equals `placeOfPoint (Point.some x y h)`.
--
--   This is the uniqueness half of the dictionary between affine points and places: a place centred at a nonsingular affine point, in the sense that $X-x$ and $Y-y$ both lie in its maximal ideal, is forced to be the place attached to that point by the genus-one gate. It is used when identifying the places obtained by restricting along isogenies and Vélu-type maps, in [`WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul`](thm.html#WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul) and [`WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2`](thm.html#WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y) (v : AlgebraicCurve.Place F W.FunctionField)
    (hX : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring.nonunits)
    (hY : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring.nonunits) :
    v = placeOfPoint (Point.some x y h) := by sorry
