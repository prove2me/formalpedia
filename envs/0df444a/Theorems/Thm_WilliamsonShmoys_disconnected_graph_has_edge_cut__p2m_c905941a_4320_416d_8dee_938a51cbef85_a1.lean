-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
-- name    : WilliamsonShmoys.disconnected_graph_has_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:26.324603+00:00
-- url     : https://prove2.me/theorems/1765af36-22c9-4dc8-89be-f4277f30642e
-- title:
--   Disconnected graph admits a nonempty edge cut
-- statement:
--   Every disconnected graph's vertices split into two nonempty disjoint sides with no edge between the sides. This is a graph-theoretic reduction, independent of planarity; use the reachable component of a vertex and its complement. The remaining work is the planar bridge construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_graph_has_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hdisconnected : ¬ K.Connected) :
    ∃ A B : Set V,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Set.univ ∧
      (∀ u, u ∈ A → ∀ v, v ∈ B → ¬ K.Adj u v) := by sorry
