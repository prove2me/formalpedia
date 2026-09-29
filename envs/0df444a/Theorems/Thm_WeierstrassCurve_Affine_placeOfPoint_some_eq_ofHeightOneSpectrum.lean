-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
-- name    : WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e603ba18-9cab-5af3-96f5-210df63b3924
-- title:
--   Centred gate: place of an affine point is the (x,y)-adic place
-- statement:
--   Let $F$ be a field and let $W$ be an affine Weierstrass curve over $F$ whose coordinate ring `W.CoordinateRing` is a Dedekind domain. Assume $W$ carries a `GenusOnePlaceGate`, that is, a bijection `pointEquivPlace` between the point set `W.Point` and the set of places of the function field `W.FunctionField` over $F$ — where a place is a valuation subring of `W.FunctionField` containing the image of $F$, distinct from the whole field, and whose ideals are all principal — together with the assertion that every such place has degree $1$; write `placeOfPoint` for this bijection. Assume moreover that the gate is centred (`GenusOnePlaceGate.IsCentred`): for every $x,y \in F$ with $W$ nonsingular at $(x,y)$, the images in `W.FunctionField` of the classes `CoordinateRing.XClass W x` and `CoordinateRing.YClass W (Polynomial.C y)` both lie in the nonunits of the valuation subring of `placeOfPoint (Point.some x y h)`. Then, given $x,y \in F$ with `h : W.Nonsingular x y` and given a height-one prime $w$ of `W.CoordinateRing` whose underlying ideal equals `CoordinateRing.XYIdeal W x (Polynomial.C y)`, the place attached by the gate to the affine point $(x,y)$ coincides with `Place.ofHeightOneSpectrum w`, the place given by the valuation subring of the $w$-adic valuation on `W.FunctionField`.
--
--   This identifies the abstract point–place dictionary of a centred genus-one gate with the geometric one on affine points: the place of $(x,y)$ is the adic place of the maximal ideal $(X-x, Y-y)$ of the coordinate ring. The prime $w$ appears as a hypothesis rather than being constructed, so that no primality argument enters the statement; callers supply it from the maximality and nonvanishing of `CoordinateRing.XYIdeal`. It is used in the extensionality result for genus-one gates and, downstream, in the comparison of points and places for period pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    placeOfPoint (Point.some x y h) = Place.ofHeightOneSpectrum (K := F) w := by sorry
