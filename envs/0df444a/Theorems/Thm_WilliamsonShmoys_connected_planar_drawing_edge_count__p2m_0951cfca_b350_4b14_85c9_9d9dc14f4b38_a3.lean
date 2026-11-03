-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:58.968211+00:00
-- url     : https://prove2.me/theorems/f80212f3-e77c-4cfe-8939-73f581dec5be
-- title:
--   Edge bound for a connected finite planar drawing
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most `3|V| − 6` edges. This retains the size and connectedness hypotheses needed for the Euler argument. The proof route is to obtain Euler’s formula for the plane embedding and count face-edge incidences, accounting for bridges in face boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
