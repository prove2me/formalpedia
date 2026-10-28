-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound
-- name    : WilliamsonShmoys.connected_graph_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:17:09.679992+00:00
-- url     : https://prove2.me/theorems/a006561d-7a89-4148-a3e4-17ec4aa1a16e
-- title:
--   Connected graph edge-count lower bound
-- statement:
--   Every finite connected graph has at least one fewer edge than vertices. This supplies the nonnegativity needed to define the parent’s face-count witness as edge count plus two minus vertex count. A direct independent proof route is Mathlib’s `Connected.card_vert_le_card_edgeSet_add_one`, using finite-cardinality simplification to translate its cardinalities to `Fintype.card` and `Set.ncard`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_edge_count_lower_bound
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by sorry
