-- Prove2me | Theorems.Thm_WilliamsonShmoys_add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- name    : WilliamsonShmoys.add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:10:48.738741+00:00
-- url     : https://prove2.me/theorems/adf325df-f128-4dd6-9a8e-98ee7f020a92
-- title:
--   Add an edge between nonreachable vertices
-- statement:
--   Adding exactly the edge {u,v} to G gives a supergraph in which u and v are reachable, while preserving an exact description of its canonically ordered edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (u v : V)
    (huv : u < v ∧ ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Reachable u v ∧
      (∀ x y, x < y →
        (K.Adj x y ↔ (G.Adj x y ∨ (x = u ∧ y = v)))) := by sorry
