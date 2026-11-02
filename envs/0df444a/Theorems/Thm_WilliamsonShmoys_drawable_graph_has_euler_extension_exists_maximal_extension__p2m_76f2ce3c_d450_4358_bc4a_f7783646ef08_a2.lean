-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- name    : WilliamsonShmoys.drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:37.787793+00:00
-- url     : https://prove2.me/theorems/97b00d21-85c3-4456-b639-3b0e033871b5
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   On a finite linearly ordered vertex type, any drawable graph has a drawable supergraph maximal among drawable supergraphs on the same vertices. The proof route is finite maximization of edge cardinality among drawable supergraphs. The assumption of at least three vertices is preserved to match the parent, though maximality itself does not require it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
