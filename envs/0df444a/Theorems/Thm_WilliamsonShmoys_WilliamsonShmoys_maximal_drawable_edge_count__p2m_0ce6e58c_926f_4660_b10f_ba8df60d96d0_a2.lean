-- Prove2me | Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- name    : WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:27.792423+00:00
-- url     : https://prove2.me/theorems/2a9c79db-1ecc-4cf4-ab9e-7f8c5fd1a388
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph with at least three vertices, maximal under drawable supergraph inclusion on the same vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hQ : HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    Q.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
