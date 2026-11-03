-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:14:59.241497+00:00
-- url     : https://prove2.me/theorems/cef82321-bd2b-4cdb-a930-0cf4542627af
-- title:
--   Edge bound for a connected finite planar drawing
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. The proof route is Euler’s formula for a connected plane graph and a lower bound of three on each face boundary length; the connectedness and size hypotheses are needed for that argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
