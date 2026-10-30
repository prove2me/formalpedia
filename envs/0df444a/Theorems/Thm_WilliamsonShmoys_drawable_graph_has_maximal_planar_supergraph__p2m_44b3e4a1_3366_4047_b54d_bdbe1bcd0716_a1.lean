-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:51.926378+00:00
-- url     : https://prove2.me/theorems/523f433a-8f4d-4aa9-adaf-daa89f661758
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that has no proper drawable supergraph. The claim follows by maximizing edge count over the finite collection of simple graphs containing G. It applies without a lower bound on the number of vertices because G itself is an eligible candidate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
