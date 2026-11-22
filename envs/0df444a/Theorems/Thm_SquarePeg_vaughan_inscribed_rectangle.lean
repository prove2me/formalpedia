-- Prove2me | Theorems.Thm_SquarePeg_vaughan_inscribed_rectangle
-- name    : SquarePeg.vaughan_inscribed_rectangle
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:20:04.743717+00:00
-- url     : https://prove2.me/theorems/26292581-3bef-469f-bf11-9ee70e2933cb
-- title:
--   Vaughan's inscribed rectangle theorem
-- statement:
--   Every Jordan curve $C$ in the plane inscribes a non-degenerate rectangle: there exist four points of $C$, in cyclic order, forming a rectangle. The aspect ratio is not prescribed. This is Vaughan's theorem, a foundational partial result toward the square peg problem that requires no regularity of the curve.
-- source:
--   Vaughan's theorem, as reported in Matschke, A survey on the square peg problem, Notices AMS 61(4) (2014), Theorem 7 (p. 350); original proof in Meyerson, Balancing acts, Topology Proc. 6 (1981), 59-75.

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem vaughan_inscribed_rectangle (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsRectangle p1 p2 p3 p4 := by sorry

end SquarePeg
