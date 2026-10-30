-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
-- name    : WilliamsonShmoys.drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:18.070763+00:00
-- url     : https://prove2.me/theorems/957d5f50-de1a-483c-adf7-e58da3f91888
-- title:
--   A drawable graph below the planar edge bound can be augmented
-- statement:
--   If a drawable finite simple graph has at least three vertices and fewer than 3n−6 edges, it has a strictly larger drawable simple supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V, K < L ∧ HasPlanarDrawingOn L := by sorry
