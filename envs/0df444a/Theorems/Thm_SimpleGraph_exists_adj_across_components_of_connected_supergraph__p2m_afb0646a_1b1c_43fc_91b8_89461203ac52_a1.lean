-- Prove2me | Theorems.Thm_SimpleGraph_exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
-- name    : SimpleGraph.exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:02.057598+00:00
-- url     : https://prove2.me/theorems/3f133009-a439-4b1c-903a-be921130931c
-- title:
--   Connected supergraph has an edge across original components
-- statement:
--   If a supergraph is connected while the original graph is disconnected, some edge of the supergraph joins vertices that were unreachable in the original graph. Prove this by taking a path between vertices in different original components and locating the first step that leaves the starting component. The statement preserves the inclusion and connectivity assumptions needed for that path argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem SimpleGraph.exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (hSub : G ≤ H) (hHConnected : H.Connected) (hGNotConnected : ¬ G.Connected) : ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
