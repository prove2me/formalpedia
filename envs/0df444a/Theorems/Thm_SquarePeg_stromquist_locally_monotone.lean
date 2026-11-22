-- Prove2me | Theorems.Thm_SquarePeg_stromquist_locally_monotone
-- name    : SquarePeg.stromquist_locally_monotone
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:22:25.365892+00:00
-- url     : https://prove2.me/theorems/f419a9bc-0dca-4302-9fdf-d236a207d51e
-- title:
--   Stromquist's locally monotone inscribed square theorem
-- statement:
--   Every locally monotone Jordan curve inscribes a non-degenerate square. A curve is locally monotone if near each of its points some linear functional is injective on the curve (equivalently, the curve is locally the graph of a continuous function over some line). This is Stromquist's theorem, one of the strongest general partial results.
-- source:
--   Stromquist, Inscribed squares and square-like quadrilaterals in closed curves, Mathematika 36 (1989), 187-197; definition and statement as in Matschke survey, Theorem 2 and preceding definition (p. 348).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem stromquist_locally_monotone (C : Set Plane) (hC : IsJordanCurve C)
    (hmono : IsLocallyMonotone C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by sorry

end SquarePeg
