-- Prove2me | Theorems.Thm_SquarePeg_square_peg_conjecture
-- name    : SquarePeg.square_peg_conjecture
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:19:33.960666+00:00
-- url     : https://prove2.me/theorems/b8da5d5a-880e-4ac8-a8d4-f2315f02a9bf
-- title:
--   Toeplitz's square peg conjecture
-- statement:
--   Every Jordan curve $C$ in the Euclidean plane inscribes a non-degenerate square: there exist four points $p_1,p_2,p_3,p_4\in C$, in cyclic order, forming a square. This is the inscribed square problem posed by Toeplitz in 1911, open in full generality. The square must have positive side length; its interior need not lie in the region bounded by $C$.
-- source:
--   Toeplitz, Ueber einige Aufgaben der Analysis situs, Verhandlungen der Schweizerischen Naturforschenden Gesellschaft (1911), 197. Statement as in Matschke, A survey on the square peg problem, Notices AMS 61(4) (2014), 346-352, Conjecture 1 (p. 346).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem square_peg_conjecture (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by sorry

end SquarePeg
