-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:35:19.261981+00:00
-- url     : https://prove2.me/theorems/a8de624e-1a6c-4973-911a-65c80278ca1b
-- title:
--   Euler face count for this connected planar drawing
-- statement:
--   Extract the finite face count of the specified crossing-free drawing of a finite connected graph and establish Euler’s formula. This removes the topological embedding and Euler-formula obligation from the parent; a proof can construct the embedded planar map from the vertex points and edge arcs and apply the connected planar map Euler formula. Connected trees are included: they have one face in the plane, and satisfy the same formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
