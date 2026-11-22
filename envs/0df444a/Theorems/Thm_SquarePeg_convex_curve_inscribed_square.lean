-- Prove2me | Theorems.Thm_SquarePeg_convex_curve_inscribed_square
-- name    : SquarePeg.convex_curve_inscribed_square
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:21:19.125257+00:00
-- url     : https://prove2.me/theorems/19756878-fc9a-451a-adc6-44e3e84ad438
-- title:
--   Inscribed square in a convex curve
-- statement:
--   Every convex Jordan curve inscribes a non-degenerate square. Here a convex curve is the boundary of a compact convex set with non-empty interior. This is the classical convex case of the square peg problem, going back to Emch and given a short proof via Fenn's table theorem.
-- source:
--   Emch, Some properties of closed convex curves in a plane, Amer. J. Math. 35 (1913), 407-412; Fenn, The table theorem, Bull. LMS 2 (1970), 73-76; Matschke survey, History (p. 347) and Fenn's Theorem 3 (p. 348).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem convex_curve_inscribed_square (C : Set Plane) (hC : IsJordanCurve C)
    (hconv : IsConvexCurve C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by sorry

end SquarePeg
