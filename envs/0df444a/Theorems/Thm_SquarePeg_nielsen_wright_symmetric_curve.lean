-- Prove2me | Theorems.Thm_SquarePeg_nielsen_wright_symmetric_curve
-- name    : SquarePeg.nielsen_wright_symmetric_curve
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:21:51.363857+00:00
-- url     : https://prove2.me/theorems/2e5d3db8-455d-4fa9-bcea-ca7120add836
-- title:
--   Inscribed square in a symmetric Jordan curve
-- statement:
--   Every Jordan curve that is symmetric across a line or about a point inscribes a non-degenerate square. This is the planar square case of the Nielsen-Wright theorem. The original result is stronger: it applies to symmetric continua in $\mathbb{R}^d$ and inscribes a rectangle similar to any prescribed rectangle, exhibiting the same symmetry; for a Jordan curve the center of point-symmetry automatically lies off the curve.
-- source:
--   Nielsen-Wright, Rectangles inscribed in symmetric continua, Geom. Dedicata 56 (1995), 285-297 (abstract); planar square case as reported in Matschke survey, History (p. 347).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem nielsen_wright_symmetric_curve (C : Set Plane) (hC : IsJordanCurve C)
    (hsym : IsLineSymmetric C ∨ IsPointSymmetric C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by sorry

end SquarePeg
