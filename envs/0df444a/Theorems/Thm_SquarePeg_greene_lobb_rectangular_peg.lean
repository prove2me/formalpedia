-- Prove2me | Theorems.Thm_SquarePeg_greene_lobb_rectangular_peg
-- name    : SquarePeg.greene_lobb_rectangular_peg
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:23:29.934749+00:00
-- url     : https://prove2.me/theorems/87a17bf2-7626-4acb-a07e-f96ddfb74249
-- title:
--   Greene-Lobb rectangular peg theorem
-- statement:
--   Every smooth Jordan curve $C$ inscribes a rectangle similar to any given rectangle $R$: for any rectangle $R$ there are four points of $C$, in cyclic order, forming a rectangle whose six pairwise distances are a common positive multiple of those of $R$. This resolves the rectangular peg problem (prescribed aspect ratio) for smooth curves.
-- source:
--   Greene-Lobb, The rectangular peg problem, Annals of Mathematics 194(2) (2021), main theorem (arXiv:2005.09193, p. 1).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem greene_lobb_rectangular_peg (C : Set Plane) (hsm : IsSmoothCurve C)
    (r1 r2 r3 r4 : Plane) (hR : IsRectangle r1 r2 r3 r4) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧
      IsRectangle p1 p2 p3 p4 ∧ SameShape p1 p2 p3 p4 r1 r2 r3 r4 := by sorry

end SquarePeg
