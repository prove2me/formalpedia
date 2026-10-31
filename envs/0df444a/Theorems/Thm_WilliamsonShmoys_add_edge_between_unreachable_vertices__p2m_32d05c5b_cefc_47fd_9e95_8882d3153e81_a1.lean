-- Prove2me | Theorems.Thm_WilliamsonShmoys_add_edge_between_unreachable_vertices__p2m_32d05c5b_cefc_47fd_9e95_8882d3153e81_a1
-- name    : WilliamsonShmoys.add_edge_between_unreachable_vertices__p2m_32d05c5b_cefc_47fd_9e95_8882d3153e81_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:13.988617+00:00
-- url     : https://prove2.me/theorems/3fe8efea-549d-4ba2-af58-c0712181ec33
-- title:
--   Add a planar edge between unreachable vertices
-- statement:
--   Given a finite planar graph and two unreachable vertices, there is a planar supergraph on the same vertices that contains the edge between them and strictly extends the original graph. Unreachability excludes the equality boundary `u = v` and ensures the requested edge is new.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.add_edge_between_unreachable_vertices__p2m_32d05c5b_cefc_47fd_9e95_8882d3153e81_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (u v : V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hNotReachable : ¬ M.Reachable u v) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.Adj u v := by sorry
