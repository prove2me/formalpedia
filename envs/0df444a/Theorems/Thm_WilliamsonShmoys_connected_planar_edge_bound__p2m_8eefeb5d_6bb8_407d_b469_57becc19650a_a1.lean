-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:52.773051+00:00
-- url     : https://prove2.me/theorems/f3754ced-64bb-4d3c-9eeb-7f444ee989e2
-- title:
--   Euler edge bound for a connected planar simple graph
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying the target’s crossing-free arc conditions has at most 3|V|−6 edges. This is the source-faithful connected case of the Euler bound and supplies the main combinatorial-topological result. A proof route establishes Euler’s formula for the embedding and counts at least three edge-sides per face, with bridges counted twice; it then translates the face-degree inequality into the edge bound. The condition |V|≥3 is essential to the simple planar bound, and connectedness is used for the Euler formula in this form.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConnected : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
