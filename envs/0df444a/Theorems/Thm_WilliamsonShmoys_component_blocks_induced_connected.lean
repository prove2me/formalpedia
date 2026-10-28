-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_blocks_induced_connected
-- name    : WilliamsonShmoys.component_blocks_induced_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:09:50.878356+00:00
-- url     : https://prove2.me/theorems/798d41d1-5a48-4303-986f-6b80a501e733
-- title:
--   Reachability blocks induce connected subgraphs
-- statement:
--   Vertices in a reachability class have paths between them. Every intermediate path vertex is reachable from the class representative, so the path lies within the class and witnesses connectedness of the induced subgraph. This is the main remaining proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_blocks_induced_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
      (G.induce (fun v => v ∈ C)).Connected := by sorry
