-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:48.285106+00:00
-- url     : https://prove2.me/theorems/ae4c30e4-5c41-43ac-8ef4-2c08b5f2ff70
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite vertex type has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. Finiteness of the set of possible simple graphs allows choosing a drawable supergraph with maximal edge count. The bound on the number of vertices is not needed here; the edge-count argument is deferred to a separate child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L < M → ¬ HasPlanarDrawingOn M) := by sorry
