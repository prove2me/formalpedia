-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_extension_adds_intercomponent_edge
-- name    : WilliamsonShmoys.connected_extension_adds_intercomponent_edge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:12:17.042426+00:00
-- url     : https://prove2.me/theorems/aa7a3b9e-401b-4b78-8303-38d97a42d42a
-- title:
--   A connected supergraph adds an edge between original components
-- statement:
--   If a connected graph contains a disconnected graph on the same finite vertex type, it has an edge joining distinct vertices that were nonadjacent in the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_extension_adds_intercomponent_edge
    {V : Type} [Fintype V]
    (J M : SimpleGraph V)
    (hJM : J ≤ M)
    (hMConnected : M.Connected)
    (hJNotConnected : ¬ J.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧ M.Adj u v := by sorry
