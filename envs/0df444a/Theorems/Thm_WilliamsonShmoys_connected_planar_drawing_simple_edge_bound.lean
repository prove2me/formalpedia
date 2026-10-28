-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_simple_edge_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_simple_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:19:45.652359+00:00
-- url     : https://prove2.me/theorems/7048d404-c5a3-4be1-882a-5a8eb51bc85d
-- title:
--   Simple planar edge bound for a connected drawing
-- statement:
--   A connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3n − 6 edges. Edges incident to the same face on both sides, such as bridges, are counted twice in the facial boundary incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_simple_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
