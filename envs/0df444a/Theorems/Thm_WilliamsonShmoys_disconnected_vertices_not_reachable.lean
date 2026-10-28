-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_reachable
-- name    : WilliamsonShmoys.disconnected_vertices_not_reachable
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T23:38:00.573838+00:00
-- url     : https://prove2.me/theorems/d0c36ddb-2bcb-4115-a5a5-3b7572adc725
-- title:
--   A disconnected finite graph has vertices in distinct components
-- statement:
--   If a finite graph is disconnected, some pair of vertices is not connected by a path. This supplies the pair used by the drawing-extension lemma; equality is excluded because reachability is reflexive.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_vertices_not_reachable
    {V : Type} [Fintype V] (H : SimpleGraph V)
    (hNotConnected : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
