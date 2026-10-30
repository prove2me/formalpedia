-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:42:04.482759+00:00
-- url     : https://prove2.me/theorems/5f6931ef-cb81-4968-a1ee-37aae830e34f
-- title:
--   Simple planar edge bound for this drawing
-- statement:
--   Prove the simple planar graph edge bound in a form without truncated subtraction. This removes the face-incidence counting obligation from the parent: count the two edge sides in face-boundary walks, show each walk has length at least three under simplicity, connectedness, and the vertex lower bound, and combine with Euler’s formula. The assumptions exclude the small connected graphs where the length-three face-boundary argument does not apply.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
