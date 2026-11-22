-- Prove2me | Theorems.Thm_SquarePeg_nielsen_inscribed_triangles
-- name    : SquarePeg.nielsen_inscribed_triangles
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:20:38.701295+00:00
-- url     : https://prove2.me/theorems/4bb229e9-d496-40dc-837f-02fc6ee82c0b
-- title:
--   Nielsen's inscribed triangles theorem
-- statement:
--   Let $C$ be a Jordan curve and $T=(t_1,t_2,t_3)$ a non-degenerate triangle, with $t_1$ a vertex of smallest angle (equivalently, the opposite side $t_2t_3$ is a shortest side). Then $C$ inscribes infinitely many triangles similar to $T$ (the set of inscribed similar triples is infinite), and the set of vertices on $C$ corresponding to $t_1$ is dense in $C$. Similarity allows reflection.
-- source:
--   Nielsen, Triangles inscribed in simple closed curves, Geom. Dedicata 43 (1992), 291-297; statement as in Matschke survey Theorem 6 (p. 350).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem nielsen_inscribed_triangles (C : Set Plane) (hC : IsJordanCurve C)
    (t1 t2 t3 : Plane) (hT : ¬ Collinear ℝ ({t1, t2, t3} : Set Plane))
    (hmin : dist t2 t3 ≤ dist t1 t2 ∧ dist t2 t3 ≤ dist t1 t3) :
    Set.Infinite {p : Plane × Plane × Plane |
      p.1 ∈ C ∧ p.2.1 ∈ C ∧ p.2.2 ∈ C ∧ SimilarTriangle p.1 p.2.1 p.2.2 t1 t2 t3} ∧
    C ⊆ closure {p1 : Plane | p1 ∈ C ∧
      ∃ p2 p3 : Plane, p2 ∈ C ∧ p3 ∈ C ∧ SimilarTriangle p1 p2 p3 t1 t2 t3} := by sorry

end SquarePeg
