-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonadjacent_vertices
-- name    : WilliamsonShmoys.disconnected_has_nonadjacent_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:38:43.211443+00:00
-- url     : https://prove2.me/theorems/6458f947-f0eb-4fb2-87b2-0efb8c908192
-- title:
--   A disconnected graph has a missing pair
-- statement:
--   A disconnected graph on a nonempty finite vertex type has two distinct nonadjacent vertices. The cardinality hypothesis ensures nonemptiness; the proof proceeds by showing that adjacency between every distinct pair would make the graph connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_nonadjacent_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ X.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ X.Adj u v := by sorry
