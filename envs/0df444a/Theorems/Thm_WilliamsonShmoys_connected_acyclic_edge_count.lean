-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_acyclic_edge_count
-- name    : WilliamsonShmoys.connected_acyclic_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:24:52.093843+00:00
-- url     : https://prove2.me/theorems/80c8ce96-855f-4f24-ae88-7bfd5b619c2f
-- title:
--   Edge count of a finite connected acyclic graph
-- statement:
--   A finite connected acyclic simple graph has exactly one fewer edge than vertices. This handles the tree boundary case separately, where the bound 3F ≤ 2|E| for face sides would not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_acyclic_edge_count
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hAcyclic : G.IsAcyclic) :
    G.edgeSet.ncard + 1 = Fintype.card V := by sorry
