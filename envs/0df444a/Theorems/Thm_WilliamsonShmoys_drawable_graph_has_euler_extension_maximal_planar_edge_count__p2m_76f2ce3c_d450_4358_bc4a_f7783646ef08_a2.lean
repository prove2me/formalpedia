-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- name    : WilliamsonShmoys.drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:44.666117+00:00
-- url     : https://prove2.me/theorems/88fa0264-c029-416b-ac57-f33f6676e9cf
-- title:
--   A maximal drawable graph has the Euler edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on that vertex set has exactly `3n − 6` edges. This isolates the planar-topology and Euler-counting step: derive connectedness and triangular faces from maximality, then apply Euler’s formula and count face-edge incidences. Its exact assumptions preserve the parent’s vertex bound and drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
