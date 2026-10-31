-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1
-- name    : WilliamsonShmoys.drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:31.850377+00:00
-- url     : https://prove2.me/theorems/ec7a7294-2e22-40b0-b436-8d0de67c32fd
-- title:
--   Planar triangulation completion at the exact edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
