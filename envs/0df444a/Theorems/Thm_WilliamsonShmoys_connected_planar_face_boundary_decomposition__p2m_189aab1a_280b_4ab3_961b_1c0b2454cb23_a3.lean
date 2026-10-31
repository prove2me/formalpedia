-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a3
-- name    : WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:47:39.918664+00:00
-- url     : https://prove2.me/theorems/1dfdc3b5-280c-4445-9049-e8c74e0b60f6
-- title:
--   Euler count and face-boundary lengths from a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a finite list of facial boundary lengths. The list length satisfies Euler’s equation, its entries sum to twice the edge count, and each entry is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a3 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ f : ℕ, ∃ lengths : List ℕ,
      f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      lengths.length = f ∧
      lengths.sum = 2 * G.edgeSet.ncard ∧
      ∀ x ∈ lengths, 3 ≤ x := by sorry
