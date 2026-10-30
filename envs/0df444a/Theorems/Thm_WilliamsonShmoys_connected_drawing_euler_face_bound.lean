-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_bound
-- name    : WilliamsonShmoys.connected_drawing_euler_face_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:51:25.615456+00:00
-- url     : https://prove2.me/theorems/bb513713-f16d-4169-9883-a012620fb50b
-- title:
--   Euler and face incidence for connected drawings
-- statement:
--   For a connected simple graph with a crossing-free plane drawing and at least three vertices, the number of faces satisfies Euler’s equation, and counting the two sides of each edge shows that three times the number of faces is at most twice the number of edges. This also covers trees: their single face has boundary length twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_euler_face_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by sorry
