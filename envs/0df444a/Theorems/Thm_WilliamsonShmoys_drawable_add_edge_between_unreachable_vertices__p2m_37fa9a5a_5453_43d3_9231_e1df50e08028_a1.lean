-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_add_edge_between_unreachable_vertices__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
-- name    : WilliamsonShmoys.drawable_add_edge_between_unreachable_vertices__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:16.9004+00:00
-- url     : https://prove2.me/theorems/7c2a912c-92cb-4df8-9259-c8c4b4cf6ccd
-- title:
--   Add a drawable edge between unreachable vertices
-- statement:
--   If two vertices lie in different connected components of a drawable finite graph, there is a drawable supergraph on the same vertices that contains their edge. The new adjacency witnesses that the supergraph is strict. The main proof route is to extend the finite planar embedding by an arc through the complement between the components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_add_edge_between_unreachable_vertices__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hUnreachable : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ L ≠ K ∧ L.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
