-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
-- name    : WilliamsonShmoys.disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:05.273722+00:00
-- url     : https://prove2.me/theorems/79b6cb48-7614-4e86-94da-1fe8fbba64b0
-- title:
--   Disconnected planar drawing admits a strict planar extension
-- statement:
--   For a finite ordered vertex type with at least three vertices, a disconnected graph with a planar drawing has a strictly larger planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ H := by sorry
